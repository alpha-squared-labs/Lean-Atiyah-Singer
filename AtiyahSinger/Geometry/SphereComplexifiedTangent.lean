/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereHodge
public import AtiyahSinger.Geometry.SphereTangentCoordinates
public import AtiyahSinger.Topology.ComplexificationBundle
public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import AtiyahSinger.Topology.EquivariantVectorBundle
public import AtiyahSinger.Topology.ExteriorBundle
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.CompactOpen

/-!
# The complexified native sphere tangent bundle and its round Hermitian metric

Public module ID: M1421.

AL02 uses the actual scalar extension of the native tangent fibers. Its topology
is the existing real/imaginary complexification topology, and its metric is the
Hermitian extension of the specified round metric. The moving-fiber action is
precisely scalar extension of the derivative of the original block action.
The even and odd exterior bundles retain their original induced topologies and
the exterior maps of that same derivative action.

Sources: Atiyah--Singer I, Lemma (3.2), pp.499--500, for the complexified tangent
Koszul complex; Husemoller, Chapter 17, section 11, for complexification;
Spin Geometry, Appendix C, for exterior compression with a Hermitian metric.
The explicit tensor carrier and conjugate-first Hermitian formula are project
realizations of these standard constructions. They do not assume a sphere index
or select a bundle from a desired K-theory identity. No fiber metric changes the
original total-space topology. Dimension zero is retained throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 25

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent sumTopology

/-- The actual complex scalar extension of each original sphere tangent fiber. -/
abbrev SphereComplexifiedTangent (r : ℕ) (x : OrthogonalSphere r) : Type :=
  ℂ ⊗[ℝ] TangentSpace (𝓡 r) x

/-- The existing complexification topology of the native real tangent bundle. -/
@[reducible]
def sphereComplexifiedTangentTopology (r : ℕ) :
    TopologicalSpace (TotalSpace Unit (SphereComplexifiedTangent r)) :=
  complexificationTopology (EuclideanSpace ℝ (Fin r))
    (fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x)

attribute [local instance] sphereComplexifiedTangentTopology

/-- The native sphere tangent complexification has finite complex rank. -/
theorem isFiniteRank_sphereComplexifiedTangent (r : ℕ) :
    IsFiniteRank (SphereComplexifiedTangent r) := by
  exact isFiniteRank_complexification (EuclideanSpace ℝ (Fin r))
    (fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x)

/-- Scalar extension of the actual sphere-action derivative between its moving fibers. -/
def sphereComplexifiedTangentAction (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r) :
    SphereComplexifiedTangent r x →ₗ[ℂ] SphereComplexifiedTangent r (A • x) :=
  (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x).toLinearMap.baseChange ℂ

/-- The specified derivative extensions form one jointly continuous moving-fiber action. -/
theorem sphereComplexifiedTangentAction_properties (r : ℕ) :
    (∀ (x : OrthogonalSphere r) (v : SphereComplexifiedTangent r x),
      (⟨(1 : Matrix.orthogonalGroup (Fin r) ℝ) • x,
        sphereComplexifiedTangentAction r 1 x v⟩ :
          TotalSpace Unit (SphereComplexifiedTangent r)) = ⟨x, v⟩) ∧
    (∀ (A B : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
        (v : SphereComplexifiedTangent r x),
      (⟨(A * B) • x, sphereComplexifiedTangentAction r (A * B) x v⟩ :
        TotalSpace Unit (SphereComplexifiedTangent r)) =
      ⟨A • (B • x), sphereComplexifiedTangentAction r A (B • x)
        (sphereComplexifiedTangentAction r B x v)⟩) ∧
    Continuous (fun p : Matrix.orthogonalGroup (Fin r) ℝ ×
        TotalSpace Unit (SphereComplexifiedTangent r) ↦
      (⟨p.1 • p.2.proj, sphereComplexifiedTangentAction r p.1 p.2.proj p.2.snd⟩ :
        TotalSpace Unit (SphereComplexifiedTangent r))) := by
  let V := EuclideanSpace ℝ (Fin r)
  let E := fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x
  let C := TotalSpace Unit (SphereComplexifiedTangent r)
  let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
  let e := complexificationDoubleTotalHomeomorph V E
  -- Scalar extension applies the same native real derivative to both Re/Im components.
  have hReIm (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
      (z : SphereComplexifiedTangent r x) :
      complexificationReIm (E (A • x)) (sphereComplexifiedTangentAction r A x z) =
        (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x
          (complexificationReIm (E x) z).1,
        mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x
          (complexificationReIm (E x) z).2) := by
    induction z using TensorProduct.inductionOn with
    | tmul a v =>
      erw [sphereComplexifiedTangentAction, LinearMap.baseChange_tmul,
        (complexificationReIm_properties (E (A • x))).1,
        (complexificationReIm_properties (E x)).1]
      simp only [ContinuousLinearMap.coe_coe, map_smul]
      rfl
    | add u v hu hv =>
      simp only [map_add, hu, hv, Prod.fst_add, Prod.snd_add]
      rfl
  have hpair {x y : OrthogonalSphere r} {u₁ u₂ : E x} {v₁ v₂ : E y}
      (h₁ : (⟨x, u₁⟩ : T) = ⟨y, v₁⟩) (h₂ : (⟨x, u₂⟩ : T) = ⟨y, v₂⟩) :
      (⟨x, (u₁, u₂)⟩ : TotalSpace (V × V) (E ×ᵇ E)) = ⟨y, (v₁, v₂)⟩ := by
    have hxy := congrArg (fun t : T ↦ t.proj) h₁
    dsimp only at hxy
    subst y
    have hu := TotalSpace.mk_injective x h₁
    have hv := TotalSpace.mk_injective x h₂
    cases hu
    cases hv
    rfl
  -- The original real tangent action laws determine the transported complex action laws.
  refine ⟨?_, ?_, ?_⟩
  · intro x v
    apply e.injective
    change (⟨(1 : Matrix.orthogonalGroup (Fin r) ℝ) • x,
      complexificationReIm (E _) (sphereComplexifiedTangentAction r 1 x v)⟩ :
        TotalSpace (V × V) (E ×ᵇ E)) = ⟨x, complexificationReIm (E x) v⟩
    rw [hReIm]
    exact hpair ((orthogonalSphereTangentMap_laws r).1 ⟨x, _⟩)
      ((orthogonalSphereTangentMap_laws r).1 ⟨x, _⟩)
  · intro A B x v
    apply e.injective
    change (⟨(A * B) • x,
      complexificationReIm (E _) (sphereComplexifiedTangentAction r (A * B) x v)⟩ :
        TotalSpace (V × V) (E ×ᵇ E)) =
      ⟨A • (B • x), complexificationReIm (E _)
        (sphereComplexifiedTangentAction r A (B • x)
          (sphereComplexifiedTangentAction r B x v))⟩
    rw [hReIm, hReIm, hReIm]
    exact hpair ((orthogonalSphereTangentMap_laws r).2 A B ⟨x, _⟩)
      ((orthogonalSphereTangentMap_laws r).2 A B ⟨x, _⟩)
  · -- Test joint continuity in the original native double-bundle topology.
    apply e.isInducing.continuous_iff.mpr
    let h := FiberBundle.Prod.isInducing_diag V E V E
    apply h.continuous_iff.mpr
    have hcoords := h.continuous.comp e.continuous
    have hc₁ : Continuous (fun p : Matrix.orthogonalGroup (Fin r) ℝ × C ↦
        p.1 • (⟨p.2.proj, (complexificationReIm (E p.2.proj) p.2.snd).1⟩ : T)) :=
      continuous_fst.smul (hcoords.fst.comp continuous_snd)
    have hc₂ : Continuous (fun p : Matrix.orthogonalGroup (Fin r) ℝ × C ↦
        p.1 • (⟨p.2.proj, (complexificationReIm (E p.2.proj) p.2.snd).2⟩ : T)) :=
      continuous_fst.smul (hcoords.snd.comp continuous_snd)
    apply (hc₁.prodMk hc₂).congr
    intro p
    dsimp only [Function.comp_apply]
    change _ = ((⟨p.1 • p.2.proj,
      (complexificationReIm (E _)
        (sphereComplexifiedTangentAction r p.1 p.2.proj p.2.snd)).1⟩ : T),
      (⟨p.1 • p.2.proj,
      (complexificationReIm (E _)
        (sphereComplexifiedTangentAction r p.1 p.2.proj p.2.snd)).2⟩ : T))
    rw [hReIm]
    rfl

/-- The original complexified derivative action packaged on the original bundle. -/
def sphereComplexifiedTangentEquivariantStructure (r : ℕ) :
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ)
      (SphereComplexifiedTangent r) where
  linearMap := sphereComplexifiedTangentAction r
  one_map := (sphereComplexifiedTangentAction_properties r).1
  mul_map := (sphereComplexifiedTangentAction_properties r).2.1
  continuous_action := (sphereComplexifiedTangentAction_properties r).2.2

/-- The conjugate-first Hermitian extension of the specified real round metric. -/
def sphereComplexifiedRoundPairing (r : ℕ) (x : OrthogonalSphere r)
    (z w : SphereComplexifiedTangent r x) : ℂ :=
  let u := complexificationReIm (TangentSpace (𝓡 r) x) z
  let v := complexificationReIm (TangentSpace (𝓡 r) x) w
  let g := orthogonalSphereRoundMetric r
  ((g.inner x u.1 v.1 + g.inner x u.2 v.2 : ℝ) : ℂ) +
    Complex.I * ((g.inner x u.1 v.2 - g.inner x u.2 v.1 : ℝ) : ℂ)

/-- The displayed round pairing is a continuous positive Hermitian metric on the same bundle. -/
theorem exists_sphereComplexifiedRoundMetric (r : ℕ) :
    ∃ h : ContinuousHermitianMetric (SphereComplexifiedTangent r),
      ∀ (x : OrthogonalSphere r) (z w : SphereComplexifiedTangent r x),
        (h.toCore x).inner z w = sphereComplexifiedRoundPairing r x z w := by
  let V := EuclideanSpace ℝ (Fin r)
  let E := fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x
  let C := SphereComplexifiedTangent r
  let g := orthogonalSphereRoundMetric r
  let q (x : OrthogonalSphere r) := complexificationReIm (E x)
  -- Compute general complex scaling in the original ordered Re/Im coordinates.
  have hsmul (x : OrthogonalSphere r) (a : ℂ) (z : C x) :
      q x (a • z) =
        (a.re • (q x z).1 - a.im • (q x z).2,
          a.im • (q x z).1 + a.re • (q x z).2) := by
    induction z using TensorProduct.inductionOn with
    | tmul b v =>
      rw [TensorProduct.smul_tmul']
      change complexificationReIm (E x) ((a * b) ⊗ₜ[ℝ] v) = _
      rw [(complexificationReIm_properties (E x)).1]
      dsimp only [q]
      rw [(complexificationReIm_properties (E x)).1]
      simp only [Complex.mul_re, Complex.mul_im, sub_smul, add_smul, smul_smul]
      exact Prod.ext rfl (add_comm _ _)
    | add u v hu hv =>
      simp only [smul_add, map_add, hu, hv, Prod.fst_add, Prod.snd_add]
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
  have hnonneg (x : OrthogonalSphere r) (v : E x) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  -- Real symmetry and positivity give the prescribed conjugate-first Hermitian form.
  let core (x : OrthogonalSphere r) : InnerProductSpace.Core ℂ (C x) :=
    { inner := sphereComplexifiedRoundPairing r x
      conj_inner_symm := by
        intro z w
        change starRingEnd ℂ
          (((g.inner x (q x w).1 (q x z).1 + g.inner x (q x w).2 (q x z).2 : ℝ) : ℂ) +
            Complex.I * ((g.inner x (q x w).1 (q x z).2 -
              g.inner x (q x w).2 (q x z).1 : ℝ) : ℂ)) = _
        simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
        rw [g.symm x (q x w).1 (q x z).1, g.symm x (q x w).2 (q x z).2,
          g.symm x (q x w).1 (q x z).2, g.symm x (q x w).2 (q x z).1]
        change _ = ((g.inner x (q x z).1 (q x w).1 +
          g.inner x (q x z).2 (q x w).2 : ℝ) : ℂ) + Complex.I *
          ((g.inner x (q x z).1 (q x w).2 - g.inner x (q x z).2 (q x w).1 : ℝ) : ℂ)
        push_cast
        ring
      re_inner_nonneg := by
        intro z
        change 0 ≤ (sphereComplexifiedRoundPairing r x z z).re
        simp only [sphereComplexifiedRoundPairing, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im,
          mul_zero, sub_zero, add_zero]
        exact add_nonneg (hnonneg x _) (hnonneg x _)
      add_left := by
        intro z w u
        change sphereComplexifiedRoundPairing r x (z + w) u = _
        simp only [sphereComplexifiedRoundPairing, map_add, Prod.fst_add, Prod.snd_add,
          add_apply]
        push_cast
        ring
      smul_left := by
        intro z w a
        change sphereComplexifiedRoundPairing r x (a • z) w =
          starRingEnd ℂ a * sphereComplexifiedRoundPairing r x z w
        change (((g.inner x (q x (a • z)).1 (q x w).1 +
          g.inner x (q x (a • z)).2 (q x w).2 : ℝ) : ℂ) + Complex.I *
          ((g.inner x (q x (a • z)).1 (q x w).2 -
            g.inner x (q x (a • z)).2 (q x w).1 : ℝ) : ℂ)) = _
        rw [hsmul]
        simp only [map_sub, map_add, map_smul, sub_apply,
          add_apply, smul_apply, smul_eq_mul]
        apply Complex.ext <;>
          simp [sphereComplexifiedRoundPairing, Complex.mul_re, Complex.mul_im, g, q] <;> ring
      definite := by
        -- A zero diagonal forces both nonnegative real summands, and both vectors, to vanish.
        intro z hz
        have hreal := congrArg Complex.re hz
        change (sphereComplexifiedRoundPairing r x z z).re = 0 at hreal
        have hd : g.inner x (q x z).1 (q x z).1 +
            g.inner x (q x z).2 (q x z).2 = 0 := by
          simpa only [sphereComplexifiedRoundPairing, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im,
            mul_zero, sub_zero, add_zero, Complex.zero_re] using hreal
        have h₁ : (q x z).1 = 0 := by
          by_contra h
          have hp := g.pos x (q x z).1 h
          linarith [hnonneg x (q x z).2]
        have h₂ : (q x z).2 = 0 := by
          by_contra h
          have hp := g.pos x (q x z).2 h
          linarith [hnonneg x (q x z).1]
        apply (q x).injective
        rw [map_zero]
        exact Prod.ext h₁ h₂ }
  -- The same native round metric pairs each of the four continuous real components.
  have hcontinuous : Continuous (fun z : TotalSpace Unit (C ×ᵇ C) ↦
      sphereComplexifiedRoundPairing r z.proj z.snd.1 z.snd.2) := by
    let e := complexificationDoubleTotalHomeomorph V E
    let d := FiberBundle.Prod.isInducing_diag V E V E
    have hcoords := d.continuous.comp e.continuous
    have h₁ := hcoords.comp (continuous_sum_fst (E := C) (F := C))
    have h₂ := hcoords.comp (continuous_sum_snd (E := C) (F := C))
    -- This native Riemannian interface preserves the existing tangent-fiber topology.
    let : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle V E :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    have h11 := h₁.fst.inner_bundle h₂.fst
    have h22 := h₁.snd.inner_bundle h₂.snd
    have h12 := h₁.fst.inner_bundle h₂.snd
    have h21 := h₁.snd.inner_bundle h₂.fst
    exact (Complex.continuous_ofReal.comp (h11.add h22)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp (h12.sub h21)))
  -- The native rank proof uses this same complexified bundle and total-space topology.
  let h : ContinuousHermitianMetric C :=
    { toCore := core
      continuous_pairing := hcontinuous
      isFiniteRank := isFiniteRank_sphereComplexifiedTangent r }
  exact ⟨h, fun x z w ↦ rfl⟩

/-- The round Hermitian metric chosen solely from its complete pairing formula. -/
def sphereComplexifiedRoundMetric (r : ℕ) :
    ContinuousHermitianMetric (SphereComplexifiedTangent r) :=
  (exists_sphereComplexifiedRoundMetric r).choose

/-- The selected metric has precisely the displayed original real/imaginary pairing. -/
theorem sphereComplexifiedRoundMetric_inner (r : ℕ) (x : OrthogonalSphere r)
    (z w : SphereComplexifiedTangent r x) :
    ((sphereComplexifiedRoundMetric r).toCore x).inner z w =
      sphereComplexifiedRoundPairing r x z w := by
  exact (exists_sphereComplexifiedRoundMetric r).choose_spec x z w

/-- The same complexified derivative preserves the same round Hermitian metric. -/
theorem sphereComplexifiedRoundMetric_invariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
    (z w : SphereComplexifiedTangent r x) :
    ((sphereComplexifiedRoundMetric r).toCore (A • x)).inner
        (sphereComplexifiedTangentAction r A x z)
        (sphereComplexifiedTangentAction r A x w) =
      ((sphereComplexifiedRoundMetric r).toCore x).inner z w := by
  -- The specified complex action is the same real derivative on both tensor coordinates.
  let E := fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x
  have hReIm (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
      (z : SphereComplexifiedTangent r x) :
      complexificationReIm (E (A • x)) (sphereComplexifiedTangentAction r A x z) =
        (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x
          (complexificationReIm (E x) z).1,
        mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x
          (complexificationReIm (E x) z).2) := by
    induction z using TensorProduct.inductionOn with
    | tmul a v =>
      erw [sphereComplexifiedTangentAction, LinearMap.baseChange_tmul,
        (complexificationReIm_properties (E (A • x))).1,
        (complexificationReIm_properties (E x)).1]
      simp only [ContinuousLinearMap.coe_coe, map_smul]
      rfl
    | add u v hu hv =>
      simp only [map_add, hu, hv, Prod.fst_add, Prod.snd_add]
      rfl
  -- Apply the original round invariance to all four real pairings in the fixed formula.
  rw [sphereComplexifiedRoundMetric_inner, sphereComplexifiedRoundMetric_inner]
  dsimp only [sphereComplexifiedRoundPairing]
  rw [hReIm A x z, hReIm A x w]
  have hInvariant (v₁ v₂ : TangentSpace (𝓡 r) x) :
      (orthogonalSphereRoundMetric r).inner (A • x)
          (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x v₁)
          (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x v₂) =
        (orthogonalSphereRoundMetric r).inner x v₁ v₂ :=
    orthogonalSphereRoundMetric_invariant r A x v₁ v₂
  rw [hInvariant, hInvariant, hInvariant, hInvariant]

attribute [local instance] exteriorTopology exteriorParityTopology

/-- The even and odd exterior bundles carry the exterior maps of the sphere-action derivative. -/
theorem exists_sphereExteriorParityEquivariantStructure (r : ℕ) (i : ZMod 2) :
    ∃ σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ)
        (fun x : OrthogonalSphere r ↦
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i),
      ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
        (a : CliffordAlgebra.evenOdd
          (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i),
        (σ.linearMap A x a : ExteriorAlgebra ℂ (SphereComplexifiedTangent r (A • x))) =
          ExteriorAlgebra.map (sphereComplexifiedTangentAction r A x) a.val := by
  -- Keep the finite-wedge continuity argument abstract until the original bundle is supplied.
  have hExterior {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
      {E : X → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      (σ : EquivariantStructure G E) :
      Continuous (fun p : G × TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)) ↦
        (⟨p.1 • p.2.proj, ExteriorAlgebra.map (σ.linearMap p.1 p.2.proj) p.2.snd⟩ :
          TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
    classical
    let A := TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x))
    let D (m : ℕ) (k : Fin m → ℕ) := TotalSpace Unit
      (fun x ↦ (Fin m → ℂ) × (∀ i : Fin m, Fin (k i) → E x))
    let dtop (m : ℕ) (k : Fin m → ℕ) : TopologicalSpace (D m k) :=
      TopologicalSpace.induced (fun z : D m k ↦ (z.proj, z.snd.1,
        (fun (i : Fin m) (j : Fin (k i)) ↦
          (⟨z.proj, z.snd.2 i j⟩ : TotalSpace Unit E)))) inferInstance
    let W (m : ℕ) (k : Fin m → ℕ) (z : D m k) : A :=
      ⟨z.proj, ∑ i : Fin m, z.snd.1 i • ExteriorAlgebra.ιMulti ℂ (k i) (z.snd.2 i)⟩
    have hW (m : ℕ) (k : Fin m → ℕ) : @Continuous (D m k) A (dtop m k) exteriorTopology (W m k) :=
      continuous_iSup_rng (i := m) (continuous_iSup_rng (i := k) continuous_coinduced_rng)
    let F (p : G × A) : A :=
      ⟨p.1 • p.2.proj, ExteriorAlgebra.map (σ.linearMap p.1 p.2.proj) p.2.snd⟩
    -- On each generator domain the same action moves the base and every wedge vector.
    have hgen (m : ℕ) (k : Fin m → ℕ) :
        letI := dtop m k
        Continuous (fun p : G × D m k ↦ F (p.1, W m k p.2)) := by
      let := dtop m k
      have hcoords : Continuous (fun z : D m k ↦ (z.proj, z.snd.1,
          (fun (i : Fin m) (j : Fin (k i)) ↦
            (⟨z.proj, z.snd.2 i j⟩ : TotalSpace Unit E)))) := continuous_induced_dom
      let L (p : G × D m k) : D m k :=
        ⟨p.1 • p.2.proj, (p.2.snd.1,
          fun i j ↦ σ.linearMap p.1 p.2.proj (p.2.snd.2 i j))⟩
      have hL : Continuous L := by
        apply continuous_induced_rng.mpr
        refine (continuous_fst.smul (hcoords.fst.comp continuous_snd)).prodMk ?_
        refine (hcoords.snd.fst.comp continuous_snd).prodMk ?_
        apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact σ.continuous_action.comp (continuous_fst.prodMk
          (((continuous_apply j).comp ((continuous_apply i).comp hcoords.snd.snd)).comp
            continuous_snd))
      apply ((hW m k).comp hL).congr
      intro p
      apply TotalSpace.ext
      · rfl
      apply heq_of_eq
      change (∑ i : Fin m, p.2.snd.1 i • ExteriorAlgebra.ιMulti ℂ (k i)
        (fun j ↦ σ.linearMap p.1 p.2.proj (p.2.snd.2 i j))) =
        ExteriorAlgebra.map (σ.linearMap p.1 p.2.proj)
          (∑ i : Fin m, p.2.snd.1 i • ExteriorAlgebra.ιMulti ℂ (k i) (p.2.snd.2 i))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, ExteriorAlgebra.map_apply_ιMulti]
      rfl
    -- Every exterior element has a finite wedge expansion in one actual fiber.
    have hcover (a : A) : ∃ (m : ℕ) (k : Fin m → ℕ) (z : D m k), W m k z = a := by
      obtain ⟨r, e, hx, he⟩ := IsFiniteRank.exists_linear_trivialization (E := E) a.proj
      let eLin : E a.proj ≃ₗ[ℂ] (Fin r → ℂ) :=
        { toFun := fun v ↦ (e ⟨a.proj, v⟩).2
          invFun := fun v ↦ cast (congrArg E (e.proj_symm_apply' hx))
            (e.toOpenPartialHomeomorph.symm (a.proj, v)).snd
          left_inv := by
            intro v
            rw [cast_eq_iff_heq]
            exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
              (e.symm_apply_mk_proj (x := ⟨a.proj, v⟩) (e.mem_source.mpr hx))
          right_inv := by
            intro v
            have hp := TotalSpace.mk_cast (F := Unit) (E := E)
              (e.proj_symm_apply' (x := v) hx) (e.toOpenPartialHomeomorph.symm (a.proj, v)).snd
            exact (congrArg (fun z : TotalSpace Unit E ↦ (e z).2) hp).trans
              (congrArg Prod.snd (e.apply_symm_apply' hx))
          map_add' := (he a.proj hx).map_add
          map_smul' := (he a.proj hx).map_smul }
      let b := ((Pi.basisFun ℂ (Fin r)).map eLin.symm).ExteriorAlgebra.reindex
        (Fintype.equivFin (Finset (Fin r)))
      let N := Fintype.card (Finset (Fin r))
      have hb (j : Fin N) : ∃ (k : ℕ) (v : Fin k → E a.proj),
          b j = ExteriorAlgebra.ιMulti ℂ k v := by
        simp only [b, Module.Basis.reindex_apply, ExteriorAlgebra.basis_apply]
        exact ⟨_, _, rfl⟩
      choose k v hv using hb
      refine ⟨N, k, ⟨a.proj, (fun j ↦ b.repr a.snd j, v)⟩, ?_⟩
      apply TotalSpace.ext
      · rfl
      apply heq_of_eq
      change (∑ j : Fin N, b.repr a.snd j • ExteriorAlgebra.ιMulti ℂ (k j) (v j)) = a.snd
      simp_rw [← hv]
      exact b.sum_repr a.snd
    -- Curry in the locally compact group; the original final topology tests continuity.
    have hpoint (a : A) : Continuous (fun g : G ↦ F (g, a)) := by
      obtain ⟨m, k, z, rfl⟩ := hcover a
      let := dtop m k
      exact (hgen m k).comp (continuous_id.prodMk continuous_const)
    let C (a : A) : C(G, A) := ⟨fun g ↦ F (g, a), hpoint a⟩
    have hC : Continuous C := by
      simp only [continuous_iSup_dom, continuous_coinduced_dom]
      intro m k
      let := dtop m k
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (hgen m k).comp continuous_swap
    exact (ContinuousMap.continuous_uncurry_of_continuous ⟨C, hC⟩).comp continuous_swap
  let E := SphereComplexifiedTangent r
  let G := Matrix.orthogonalGroup (Fin r) ℝ
  let σ : EquivariantStructure G E := sphereComplexifiedTangentEquivariantStructure r
  let : IsFiniteRank E := isFiniteRank_sphereComplexifiedTangent r
  -- The original matrix topology makes the closed orthogonal subgroup locally compact.
  let : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → ℝ))
  let : LocallyCompactSpace G := isClosed_unitary.locallyCompactSpace
  have hc : Continuous (fun p : G × TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)) ↦
      (⟨p.1 • p.2.proj, ExteriorAlgebra.map (σ.linearMap p.1 p.2.proj) p.2.snd⟩ :
        TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := hExterior σ
  let P (x : OrthogonalSphere r) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
  -- Exterior functoriality preserves the original parity submodules.
  have hmap (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r) :
      (P x).map (ExteriorAlgebra.map (σ.linearMap A x)).toLinearMap = P (A • x) := by
    have hr : LinearMap.range (σ.linearMap A x) = ⊤ :=
      LinearMap.range_eq_top.mpr (σ.linearMap_bijective A x).2
    simp only [P, CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow,
      ExteriorAlgebra.ι_range_map_map, hr, Submodule.map_top]
  let L (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r) :
      P x →ₗ[ℂ] P (A • x) :=
    ((ExteriorAlgebra.map (σ.linearMap A x)).toLinearMap.comp (P x).subtype).codRestrict
      (P (A • x)) (fun a ↦ by
        rw [← hmap A x]
        exact ⟨a.val, a.property, rfl⟩)
  -- Transport action identities as total-space equalities, retaining their moving base points.
  have hlift {x y z : OrthogonalSphere r} (f : E x →ₗ[ℂ] E y) (g : E x →ₗ[ℂ] E z)
      (h : ∀ v, (⟨y, f v⟩ : TotalSpace Unit E) = ⟨z, g v⟩)
      (a : ExteriorAlgebra ℂ (E x)) :
      (⟨y, ExteriorAlgebra.map f a⟩ :
        TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x))) =
      ⟨z, ExteriorAlgebra.map g a⟩ := by
    have hyz := congrArg (fun t : TotalSpace Unit E ↦ t.proj) (h 0)
    dsimp only at hyz
    subst z
    have hfg : f = g := by
      apply LinearMap.ext
      intro v
      exact TotalSpace.mk_injective y (h v)
    rw [hfg]
  have hinj : Function.Injective (fun a : TotalSpace Unit (fun x ↦ P x) ↦
      (⟨a.proj, a.snd.val⟩ : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
    rintro ⟨x, a⟩ ⟨y, b⟩ h
    have hxy := congrArg (fun t : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)) ↦
      t.proj) h
    dsimp only at hxy
    subst y
    have hab : a = b := Subtype.ext (TotalSpace.mk_injective x h)
    cases hab
    rfl
  refine ⟨{ linearMap := L, one_map := ?_, mul_map := ?_, continuous_action := ?_ },
    fun A x a ↦ rfl⟩
  · clear_value σ
    intro x a
    apply hinj
    change (⟨(1 : Matrix.orthogonalGroup (Fin r) ℝ) • x,
      ExteriorAlgebra.map (σ.linearMap 1 x) a.val⟩ :
        TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x))) = ⟨x, a.val⟩
    have h := hlift (σ.linearMap 1 x) LinearMap.id (σ.one_map x) a.val
    simpa only [ExteriorAlgebra.map_id, AlgHom.id_apply] using h
  · clear_value σ
    intro A B x a
    apply hinj
    change (⟨(A * B) • x, ExteriorAlgebra.map (σ.linearMap (A * B) x) a.val⟩ :
      TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x))) =
      ⟨A • (B • x), ExteriorAlgebra.map (σ.linearMap A (B • x))
        (ExteriorAlgebra.map (σ.linearMap B x) a.val)⟩
    have h := hlift (σ.linearMap (A * B) x)
      ((σ.linearMap A (B • x)).comp (σ.linearMap B x)) (σ.mul_map A B x) a.val
    simpa only [← ExteriorAlgebra.map_comp_map, AlgHom.comp_apply] using h
  · -- Restrict the continuous exterior action through the original parity inclusion.
    clear_value σ
    apply continuous_induced_rng.mpr
    have hi : Continuous (fun a : TotalSpace Unit (fun x ↦ P x) ↦
        (⟨a.proj, a.snd.val⟩ : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) :=
      continuous_induced_dom
    change Continuous (fun p : Matrix.orthogonalGroup (Fin r) ℝ ×
      TotalSpace Unit (fun x ↦ P x) ↦
      (⟨p.1 • p.2.proj, ExteriorAlgebra.map (σ.linearMap p.1 p.2.proj) p.2.snd.val⟩ :
        TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x))))
    convert hc.comp (continuous_fst.prodMk (hi.comp continuous_snd)) using 1
    rfl

/-- The same exterior maps, with action and continuity fields on the original parity bundle. -/
def sphereExteriorParityEquivariantStructure (r : ℕ) (i : ZMod 2) :
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ)
      (fun x : OrthogonalSphere r ↦
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i) :=
  (exists_sphereExteriorParityEquivariantStructure r i).choose

/-- The parity action is exactly the exterior map of the same complexified derivative. -/
theorem sphereExteriorParityEquivariantStructure_apply (r : ℕ) (i : ZMod 2)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
    (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i) :
    ((sphereExteriorParityEquivariantStructure r i).linearMap A x a :
        ExteriorAlgebra ℂ (SphereComplexifiedTangent r (A • x))) =
      ExteriorAlgebra.map (sphereComplexifiedTangentAction r A x) a.val := by
  exact (exists_sphereExteriorParityEquivariantStructure r i).choose_spec A x a

end AtiyahSinger
