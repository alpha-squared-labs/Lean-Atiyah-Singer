/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SmoothFiniteRepresentation
public import AtiyahSinger.Geometry.EquivariantIdempotentSmoothing
public import AtiyahSinger.Geometry.EquivariantSmoothIdempotentBundle
public import AtiyahSinger.Topology.EquivariantBundleEmbedding

/-!
# Smooth equivariant finite image models

Public module ID: M1208.

For a compact finite-dimensional Lie group acting smoothly on a compact base,
an original continuous equivariant finite bundle is isomorphic to the actual
image of a smooth equivariant idempotent in a finite
representation. The construction retains the same representation throughout
smooth approximation, Haar averaging, analytic correction and local frame
construction. Both constant-rank native smoothing and variable-rank atlas
smoothing reuse this same model and its specified equivariant isomorphism.
-/

@[expose] public noncomputable section

universe u

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff Matrix

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]

attribute [local instance] trivialTopology

include hDim hLie hGC hGT hM hT hSC hC hAction hE

omit hSC in
open Classical in
/-- Every original finite equivariant bundle has a smooth equivariant finite image model. -/
theorem EquivariantStructure.exists_smooth_image_model (σ : EquivariantStructure G E) :
    ∃ p : IdempotentMatrix C(M, ℂ),
      letI := IdempotentMatrix.fiberTotalSpaceTopology p
      ∃ τ : EquivariantStructure G (fun x ↦ p.fiber x),
        ∃ e : Iso E (fun x ↦ p.fiber x), e.IsEquivariant σ τ ∧
          ∃ B : SmoothComplexBundleAtlas.{u} (n := n) (fun x ↦ p.fiber x),
            ∀ (i j : B.Index) (k : Fin (B.rank i)),
              ContMDiffOn (𝓘(ℝ, VG).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
                𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
                (fun z : G × M ↦ if hx : z.2 ∈ (B.chart i).baseSet then
                  (B.chart j ⟨z.1 • z.2,
                    τ.linearMap z.1 z.2 ((B.frameLinearEquiv i z.2 hx).symm
                      (Pi.single k 1))⟩).2 else 0)
                {z : G × M | z.2 ∈ (B.chart i).baseSet ∧
                  z.1 • z.2 ∈ (B.chart j).baseSet} := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let IG := 𝓘(ℝ, VG)
  -- Embed the original bundle in a genuine finite representation and average
  -- projections onto exactly that image. No invariant measure on M is used.
  obtain ⟨κ, q, hq, heq⟩ := σ.exists_finiteRepresentation_embedding
  let V := Fin κ.dimension → ℂ
  obtain ⟨P, hP, hfix, hrange, hcov⟩ := q.exists_equivariant_projection_range σ κ hq heq
  have hPP (x : M) : P x * P x = P x := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := hrange x v
    change P x (P x v) = P x v
    rw [hw, hfix]
  have hPcov (g : G) (x : M) :
      P (g • x) * κ.representation g = κ.representation g * P x :=
    ContinuousLinearMap.ext (hcov g x)
  -- Automatic smoothness of the same finite representation gives smooth
  -- matrix columns; finite basis reconstruction gives operator smoothness.
  have hκ : ContMDiff IG 𝓘(ℝ, V →L[ℂ] V) ∞ (fun g ↦ κ.representation g) := by
    let b := Pi.basisFun ℂ (Fin κ.dimension)
    let C₀ : (Fin κ.dimension → V) ≃ₗ[ℂ] (V →L[ℂ] V) :=
      (b.constr ℂ).trans LinearMap.toContinuousLinearMap
    let C : (Fin κ.dimension → V) →L[ℝ] (V →L[ℂ] V) :=
      C₀.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
    have hc := C.contMDiff.comp (contMDiff_pi_space.mpr fun i ↦
      κ.contMDiff_action.comp (contMDiff_id.prodMk contMDiff_const :
        ContMDiff IG (IG.prod 𝓘(ℝ, V)) ∞ (fun g : G ↦ (g, b i))))
    apply hc.congr
    intro g
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    exact (b.constr_basis ℂ (fun j ↦ κ.representation g (b j)) i).symm
  obtain ⟨Q, hQ, hQQ, hQcov, hunit⟩ :=
    exists_smooth_equivariant_idempotent (n := n) (M := M) κ.representation hκ P hP hPP hPcov
  -- The canonical intertwiner is invertible on the fixed ambient space and
  -- carries the old image to the corrected smooth image, equivariantly.
  let H (x : M) : V →L[ℂ] V := idempotentIntertwiner (Q x) (P x)
  have hH : Continuous H := by
    dsimp only [H, idempotentIntertwiner]
    exact ((continuous_const.sub hQ.continuous).sub hP).add
      ((continuous_const.mul hQ.continuous).mul hP)
  have hHP (x : M) : H x * P x = Q x * H x :=
    idempotentIntertwiner_mul (Q x) (P x) (hQQ x) (hPP x)
  have hHcov (g : G) (x : M) :
      H (g • x) * κ.representation g = κ.representation g * H x := by
    have hprod : Q (g • x) * P (g • x) * κ.representation g =
        κ.representation g * Q x * P x := by
      rw [mul_assoc, hPcov, ← mul_assoc, hQcov, mul_assoc]
    dsimp only [H, idempotentIntertwiner]
    noncomm_ring [hPcov g x, hQcov g x, hprod]
  let A (x : M) : Matrix (Fin κ.dimension) (Fin κ.dimension) ℂ :=
    LinearMap.toMatrix' (Q x).toLinearMap
  have hA (i j : Fin κ.dimension) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun x ↦ A x i j) := by
    let ev₀ : (V →L[ℂ] V) →ₗ[ℂ] ℂ := {
      toFun L := L (Pi.single j 1) i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    let ev : (V →L[ℂ] V) →L[ℝ] ℂ := ev₀.toContinuousLinearMap.restrictScalars ℝ
    exact ev.contMDiff.comp hQ
  have hAA (x : M) : A x * A x = A x := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact congrArg ContinuousLinearMap.toLinearMap (hQQ x)
  let p : IdempotentMatrix C(M, ℂ) := {
    size := κ.dimension
    matrix i j := ⟨fun x ↦ A x i j, (hA i j).continuous⟩
    mul_self := by
      ext i j x
      change (∑ k : Fin κ.dimension,
        (⟨fun y ↦ A y i k, (hA i k).continuous⟩ : C(M, ℂ)) *
          (⟨fun y ↦ A y k j, (hA k j).continuous⟩ : C(M, ℂ))) x = A x i j
      simpa [Matrix.mul_apply] using congrFun (congrFun (hAA x) i) j }
  let := IdempotentMatrix.fiberTotalSpaceTopology p
  let := IdempotentMatrix.isFiniteRank_fiber p
  have hmat (x : M) (v : V) :
      (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix *ᵥ v = Q x v :=
    LinearMap.toMatrix'_mulVec (Q x).toLinearMap v
  have hmem (x : M) (v : V) : v ∈ p.fiber x ↔ Q x v = v := by
    constructor
    · rintro ⟨w, hw⟩
      have hw' : Q x w = v := (hmat x w).symm.trans hw
      rw [← hw']
      exact DFunLike.congr_fun (hQQ x) w
    · intro hv
      exact ⟨v, (hmat x v).trans hv⟩
  let J : Hom E (fun x ↦ p.fiber x) := {
    linearMap x := {
      toFun v := ⟨H x (q.linearMap x v), (hmem x _).mpr (by
        have h := DFunLike.congr_fun (hHP x) (q.linearMap x v)
        change H x (P x (q.linearMap x v)) = Q x (H x (q.linearMap x v)) at h
        rw [hfix] at h
        exact h.symm)⟩
      map_add' v w := by apply Subtype.ext; simp [map_add]
      map_smul' a v := by apply Subtype.ext; simp [map_smul] }
    continuous_total := by
      apply continuous_induced_rng.mpr
      exact (continuous_proj (E := E)).prodMk
        ((hH.comp (continuous_proj (E := E))).clm_apply
          (continuous_induced_rng.mp q.continuous_total).snd) }
  have hJ (x : M) : Function.Bijective (J.linearMap x) := by
    have hHbij := ContinuousLinearMap.isUnit_iff_bijective.mp (hunit x)
    constructor
    · intro v w hvw
      exact hq x (hHbij.injective (congrArg Subtype.val hvw))
    · intro w
      obtain ⟨u, hu⟩ := hHbij.surjective w.val
      have hPu : P x u = u := hHbij.injective (by
        have ht := DFunLike.congr_fun (hHP x) u
        change H x (P x u) = Q x (H x u) at ht
        rw [hu, (hmem x w.val).mp w.property] at ht
        exact ht.trans hu.symm)
      obtain ⟨v, hv⟩ := hrange x u
      refine ⟨v, Subtype.ext ?_⟩
      change H x (q.linearMap x v) = w.val
      rw [← hv, hPu, hu]
  let e := J.toIso hJ
  have hcoords : Continuous (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦
      (z.proj, z.snd.val)) := continuous_induced_dom
  have hcoords_inj : Function.Injective
      (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦ (z.proj, z.snd.val)) := by
    rintro ⟨x, u⟩ ⟨y, v⟩ h
    obtain ⟨rfl, huv⟩ := Prod.mk.inj h
    exact congrArg (TotalSpace.mk x) (Subtype.ext huv)
  let τ : EquivariantStructure G (fun x ↦ p.fiber x) := {
    linearMap g x := {
      toFun v := ⟨κ.representation g v.val, (hmem (g • x) _).mpr (by
        have hc := DFunLike.congr_fun (hQcov g x) v.val
        change Q (g • x) (κ.representation g v.val) = κ.representation g (Q x v.val) at hc
        rw [(hmem x v.val).mp v.property] at hc
        exact hc)⟩
      map_add' u v := by apply Subtype.ext; exact map_add (κ.representation g) u.val v.val
      map_smul' a v := by apply Subtype.ext; exact map_smul (κ.representation g) a v.val }
    one_map x v := by
      apply hcoords_inj
      change ((1 : G) • x, κ.representation 1 v.val) = (x, v.val)
      simp
    mul_map g h x v := by
      apply hcoords_inj
      change ((g * h) • x, κ.representation (g * h) v.val) =
        (g • (h • x), κ.representation g (κ.representation h v.val))
      simp [map_mul, mul_smul, mul_apply_eq_comp]
    continuous_action := continuous_induced_rng.mpr
      ((continuous_fst.smul (hcoords.fst.comp continuous_snd)).prodMk
        (κ.continuous_action.comp
          (continuous_fst.prodMk (hcoords.snd.comp continuous_snd)))) }
  have he : e.IsEquivariant σ τ := by
    intro g x v
    apply Subtype.ext
    change H (g • x) (q.linearMap (g • x) (σ.linearMap g x v)) =
      κ.representation g (H x (q.linearMap x v))
    have heq' : q.linearMap (g • x) (σ.linearMap g x v) =
        κ.representation g (q.linearMap x v) := heq g x v
    rw [heq']
    exact DFunLike.congr_fun (hHcov g x) (q.linearMap x v)
  -- The explicit local image frames certify this precise restricted action
  -- as smooth in all ranks, before any fixed-rank native model is chosen.
  obtain ⟨B, hB⟩ := p.exists_smoothAtlas_of_ambient_action IG hA
    κ.representation κ.contMDiff_action τ (fun _ _ _ ↦ rfl)
  exact ⟨p, τ, e, he, B, hB⟩

end AtiyahSinger.ComplexBundle
