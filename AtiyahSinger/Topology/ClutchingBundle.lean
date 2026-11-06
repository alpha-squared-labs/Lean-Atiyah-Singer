/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTotalPullback
public import AtiyahSinger.Topology.BundleTriple
public import AtiyahSinger.Topology.DoubleSpace
public import Mathlib.Analysis.Complex.Tietze

/-!
# Clutching along the closed seam of a double

Public module ID: M1617.

D07/K02. On a compact Hausdorff base with a closed seam, SG I.9.25 glues E
on the left copy to F on the right using the specified boundary isomorphism.
A chosen bundle is accompanied by two restriction charts
and their exact seam equation. This characterizes the descent data rather than
merely choosing some bundle with a prescribed absolute K class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology
open scoped Matrix unitInterval

variable {X : Type*} [TopologicalSpace X] {A : Set X}

attribute [local instance] sumTopology isFiniteRank_sum
  IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber isFiniteRank_pullback


/-- The two restriction charts identify seam vectors by the given boundary map. -/
def ClutchingCompatible (a : BundleTriple A) (W : FiniteBundle (DoubleSpace A))
    (eL : Iso ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ W.Fiber) a.source.Fiber)
    (eR : Iso ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ W.Fiber) a.target.Fiber) :
    Prop :=
  ∀ x : A, ∀ v : a.source.Fiber x,
    eR.linearEquiv x
      (cast (congrArg W.Fiber (DoubleSpace.left_eq_right A x))
        ((eL.linearEquiv x).symm v)) = a.boundary.linearEquiv x v

variable [hX : CompactSpace X] [hT : T2Space X]
include hX hT

set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency false in
/-- The specified boundary isomorphism admits a finite-rank glued bundle. -/
theorem exists_clutchingBundle (hA : IsClosed A) (a : BundleTriple A) :
    ∃ W : FiniteBundle (DoubleSpace A),
      ∃ eL : Iso ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ W.Fiber) a.source.Fiber,
        ∃ eR : Iso ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ W.Fiber) a.target.Fiber,
          ClutchingCompatible a W eL eR := by
  classical
  have extension (p q : IdempotentMatrix C(X, ℂ))
      (a : Hom ((Subtype.val : A → X) *ᵖ fun x ↦ p.fiber x)
        ((Subtype.val : A → X) *ᵖ fun x ↦ q.fiber x)) :
      ∃ L : Matrix (Fin q.size) (Fin p.size) C(X, ℂ),
        ∀ (x : A) (v : Fin p.size → ℂ),
          (fun i j ↦ L i j x.val) *ᵥ v =
            (a.linearMap x
              ⟨(p.map (ContinuousMap.evalAlgHom ℂ ℂ x.val).toRingHom).matrix *ᵥ v,
                ⟨v, rfl⟩⟩).val := by
    classical
    let P (x : X) : Matrix (Fin p.size) (Fin p.size) ℂ :=
      (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix
    let proj (x : X) : (Fin p.size → ℂ) →ₗ[ℂ] p.fiber x :=
      (P x).mulVecLin.rangeRestrict
    let L₀ (x : A) : (Fin p.size → ℂ) →ₗ[ℂ] (Fin q.size → ℂ) :=
      (q.fiber x.val).subtype.comp ((a.linearMap x).comp (proj x.val))
    -- Project the standard constant columns into the original image bundle over the seam.
    have hP : Continuous P :=
      continuous_pi (fun i ↦ continuous_pi (fun j ↦ (p.matrix i j).continuous))
    have hcolumn (j : Fin p.size) : Continuous
        (fun x : A ↦ (⟨x, proj x.val (Pi.single j 1)⟩ :
          TotalSpace Unit ((Subtype.val : A → X) *ᵖ fun x ↦ p.fiber x))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit (fun x ↦ p.fiber x)
        (Subtype.val : A → X)).continuous_iff]
      refine continuous_id.prodMk ?_
      apply continuous_induced_rng.mpr
      change Continuous (fun x : A ↦ (x.val, P x.val *ᵥ Pi.single j (1 : ℂ)))
      exact continuous_subtype_val.prodMk
        ((hP.comp continuous_subtype_val).matrix_mulVec continuous_const)
    -- Apply the same supplied boundary Hom, then read its original ambient coordinates.
    have hL₀ (i : Fin q.size) (j : Fin p.size) :
        Continuous (fun x : A ↦ (L₀ x (Pi.single j 1)) i) := by
      have h := (Pullback.continuous_lift Unit (fun x ↦ q.fiber x)
        (Subtype.val : A → X)).comp (a.continuous_total.comp (hcolumn j))
      have hcoords := (continuous_induced_dom : Continuous
        (fun z : TotalSpace Unit (fun x ↦ q.fiber x) ↦ (z.proj, z.snd.val))).comp h
      exact (continuous_apply i).comp hcoords.snd
    -- Tietze is applied entrywise; no claim of invertibility away from the seam is needed.
    choose L hL using fun i j ↦
      (⟨fun x : A ↦ (L₀ x (Pi.single j 1)) i, hL₀ i j⟩ : C(A, ℂ)).exists_restrict_eq hA
    refine ⟨L, ?_⟩
    intro x v
    have hmatrix : (fun i j ↦ L i j x.val) = LinearMap.toMatrix' (L₀ x) := by
      ext i j
      exact congrArg (fun f : C(A, ℂ) ↦ f x) (hL i j)
    rw [hmatrix, LinearMap.toMatrix'_mulVec]
    rfl
  have imageIso {Y : Type _} [TopologicalSpace Y]
      (p : IdempotentMatrix C(X, ℂ)) (q : IdempotentMatrix C(Y, ℂ)) (f : C(X, Y))
      (M : X → Matrix (Fin q.size) (Fin p.size) ℂ)
      (N : X → Matrix (Fin p.size) (Fin q.size) ℂ) (hM : Continuous M)
      (hNM : ∀ x, N x * M x = (fun i j ↦ p.matrix i j x))
      (hMN : ∀ x, M x * N x =
        (fun i j ↦ q.matrix i j (f x))) :
      ∃ e : Iso (fun x ↦ p.fiber x) ((f : X → Y) *ᵖ (fun y ↦ q.fiber y)),
        ∀ x v, (e.linearEquiv x v).val = M x *ᵥ v.val := by
    classical
    -- Idempotence fixes precisely the original image vectors.
    have fixed (n : ℕ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : P * P = P)
        (v : P.mulVecLin.range) : P *ᵥ v.val = v.val := by
      obtain ⟨w, hw⟩ := v.property
      change P *ᵥ w = v.val at hw
      rw [← hw, Matrix.mulVec_mulVec, hP]
    have fp (x : X) (v : p.fiber x) : (fun i j ↦ p.matrix i j x) *ᵥ v.val = v.val :=
      fixed p.size _ (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self v
    have fq (y : Y) (v : q.fiber y) : (fun i j ↦ q.matrix i j y) *ᵥ v.val = v.val :=
      fixed q.size _ (q.map (ContinuousMap.evalAlgHom ℂ ℂ y).toRingHom).mul_self v
    let g (x : X) : p.fiber x →ₗ[ℂ] q.fiber (f x) :=
      ((M x).mulVecLin.comp (p.fiber x).subtype).codRestrict (q.fiber (f x)) (by
        intro v
        refine ⟨M x *ᵥ v.val, ?_⟩
        change (fun i j ↦ q.matrix i j (f x)) *ᵥ (M x *ᵥ v.val) = M x *ᵥ v.val
        rw [← hMN x, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec v.val (N x), hNM x,
          fp x v])
    let G : Hom (fun x ↦ p.fiber x) ((f : X → Y) *ᵖ (fun y ↦ q.fiber y)) :=
      { linearMap := g
        continuous_total := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (fun y ↦ q.fiber y) f).continuous_iff]
          have hp : Continuous (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦
              (z.proj, z.snd.val)) := continuous_induced_dom
          refine hp.fst.prodMk (continuous_induced_rng.mpr ?_)
          refine (f.continuous.comp hp.fst).prodMk ?_
          change Continuous (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦
            M z.proj *ᵥ z.snd.val)
          exact (hM.comp hp.fst).matrix_mulVec hp.snd }
    have hbij (x : X) : Function.Bijective (G.linearMap x) := by
      constructor
      · intro v w hvw
        apply Subtype.ext
        have hv := congrArg (fun z : q.fiber (f x) ↦ N x *ᵥ z.val) hvw
        change N x *ᵥ (M x *ᵥ v.val) = N x *ᵥ (M x *ᵥ w.val) at hv
        simpa only [Matrix.mulVec_mulVec, hNM x, fp x v, fp x w] using hv
      · intro w
        have hm : N x *ᵥ w.val ∈ p.fiber x := by
          refine ⟨N x *ᵥ w.val, ?_⟩
          change (fun i j ↦ p.matrix i j x) *ᵥ (N x *ᵥ w.val) = N x *ᵥ w.val
          rw [← hNM x, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec w.val (M x), hMN x,
            fq (f x) w]
        refine ⟨⟨N x *ᵥ w.val, hm⟩, ?_⟩
        apply Subtype.ext
        change M x *ᵥ (N x *ᵥ w.val) = w.val
        rw [Matrix.mulVec_mulVec, hMN x, fq (f x) w]
    exact ⟨G.toIso hbij, fun _ _ ↦ rfl⟩
  -- Stabilized elementary matrices realize the closed-seam gluing inside one trivial bundle.
  -- Use the original continuous bundle presentations and the original boundary isomorphism.
  let p := idempotentPresentation (E := a.source.Fiber)
  let q := idempotentPresentation (E := a.target.Fiber)
  let ep : Iso a.source.Fiber (fun x ↦ p.fiber x) := presentationIso
  let eq : Iso a.target.Fiber (fun x ↦ q.fiber x) := presentationIso
  let d : Iso (Restrict (fun x ↦ p.fiber x) A) (Restrict (fun x ↦ q.fiber x) A) :=
    (ep.symm.restrict A).trans (a.boundary.trans (eq.restrict A))
  obtain ⟨Lc, hLc⟩ := extension p q d.toHom
  obtain ⟨Bc, hBc⟩ := extension q p d.symm.toHom
  dsimp only [IdempotentMatrix.map] at hLc hBc
  let P (x : X) : Matrix (Fin p.size) (Fin p.size) ℂ := fun i j ↦ p.matrix i j x
  let Q (x : X) : Matrix (Fin q.size) (Fin q.size) ℂ := fun i j ↦ q.matrix i j x
  let L (x : X) : Matrix (Fin q.size) (Fin p.size) ℂ := fun i j ↦ Lc i j x
  let B (x : X) : Matrix (Fin p.size) (Fin q.size) ℂ := fun i j ↦ Bc i j x
  have hP (x : X) : P x * P x = P x :=
    (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  have hQ (x : X) : Q x * Q x = Q x :=
    (q.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  have hPc : Continuous P := continuous_matrix (fun i j ↦ (p.matrix i j).continuous)
  have hQc : Continuous Q := continuous_matrix (fun i j ↦ (q.matrix i j).continuous)
  have hLc' : Continuous L := continuous_matrix (fun i j ↦ (Lc i j).continuous)
  have hBc' : Continuous B := continuous_matrix (fun i j ↦ (Bc i j).continuous)
  have hpfix (x : X) (v : p.fiber x) : P x *ᵥ v.val = v.val := by
    obtain ⟨w, hw⟩ := v.property
    change Fin p.size → ℂ at w
    change P x *ᵥ w = v.val at hw
    rw [← hw, Matrix.mulVec_mulVec, hP]
  have hqfix (x : X) (v : q.fiber x) : Q x *ᵥ v.val = v.val := by
    obtain ⟨w, hw⟩ := v.property
    change Fin q.size → ℂ at w
    change Q x *ᵥ w = v.val at hw
    rw [← hw, Matrix.mulVec_mulVec, hQ]
  have hL (x : A) (v : p.fiber x) : L x *ᵥ v.val = (d.linearEquiv x v).val := by
    have h := hLc x v.val
    change L x *ᵥ v.val = (d.linearEquiv x ⟨P x *ᵥ v.val, _⟩).val at h
    simpa only [hpfix x v] using h
  have hB (x : A) (v : q.fiber x) : B x *ᵥ v.val = ((d.linearEquiv x).symm v).val := by
    have h := hBc x v.val
    change B x *ᵥ v.val = ((d.linearEquiv x).symm ⟨Q x *ᵥ v.val, _⟩).val at h
    simpa only [hqfix x v] using h
  have hBL (x : A) : B x * L x = P x := by
    apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, hLc x v]
    change B x *ᵥ (d.linearEquiv x ⟨P x *ᵥ v, _⟩).val = P x *ᵥ v
    erw [hB, LinearEquiv.symm_apply_apply]
  have hLB (x : A) : L x * B x = Q x := by
    apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, hBc x v]
    change L x *ᵥ ((d.linearEquiv x).symm ⟨Q x *ᵥ v, _⟩).val = Q x *ᵥ v
    erw [hL, LinearEquiv.apply_symm_apply]
  have hLp (x : A) : L x * P x = L x := by
    apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, hLc x (P x *ᵥ v), hLc x v]
    apply congrArg (fun w : p.fiber x ↦ (d.linearEquiv x w).val)
    apply Subtype.ext
    change P x *ᵥ (P x *ᵥ v) = P x *ᵥ v
    rw [Matrix.mulVec_mulVec, hP]
  have hqL (x : A) : Q x * L x = L x := by
    apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, hLc x v]
    exact hqfix x _
  have hpB (x : A) : P x * B x = B x := by
    apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, hBc x v]
    exact hpfix x _
  -- Three elementary shears are invertible everywhere, without any inverse extension claim.
  let S (x : X) : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) ℂ :=
    Matrix.fromBlocks 1 (-B x) 0 1
  let T (x : X) : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) ℂ :=
    Matrix.fromBlocks 1 0 (L x) 1
  let S' (x : X) : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) ℂ :=
    Matrix.fromBlocks 1 (B x) 0 1
  let T' (x : X) : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) ℂ :=
    Matrix.fromBlocks 1 0 (-L x) 1
  let U (x : X) := S x * T x * S x
  let V (x : X) := S' x * T' x * S' x
  have hSS (x : X) : S x * S' x = 1 := by
    simp [S, S', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hS'S (x : X) : S' x * S x = 1 := by
    simp [S, S', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hTT (x : X) : T x * T' x = 1 := by
    simp [T, T', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hT'T (x : X) : T' x * T x = 1 := by
    simp [T, T', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hUV (x : X) : U x * V x = 1 := by
    change (S x * T x * S x) * (S' x * T' x * S' x) = 1
    calc
      _ = S x * T x * (S x * S' x) * T' x * S' x := by noncomm_ring
      _ = 1 := by rw [hSS, mul_one, mul_assoc (S x) (T x) (T' x), hTT, mul_one, hSS]
  have hVU (x : X) : V x * U x = 1 := by
    change (S' x * T' x * S' x) * (S x * T x * S x) = 1
    calc
      _ = S' x * T' x * (S' x * S x) * T x * S x := by noncomm_ring
      _ = 1 := by rw [hS'S, mul_one, mul_assoc (S' x) (T' x) (T x), hT'T, mul_one, hS'S]
  have hU (x : A) : U x = Matrix.fromBlocks (1 - P x) (-B x) (L x) (1 - Q x) := by
    simp only [U, S, T, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, zero_add, add_zero, Matrix.neg_mul, Matrix.mul_neg, hBL, hLB]
    congr 1
    · simp [Matrix.add_mul, Matrix.neg_mul, hpB]
    · abel
  let P₀ (x : X) : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) ℂ :=
    Matrix.fromBlocks (P x) 0 0 0
  let Q₀ (x : X) : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) ℂ :=
    Matrix.fromBlocks 0 0 0 (Q x)
  have hP₀ (x : X) : P₀ x * P₀ x = P₀ x := by
    simp [P₀, Matrix.fromBlocks_multiply, hP]
  have hQ₀ (x : X) : Q₀ x * Q₀ x = Q₀ x := by
    simp [Q₀, Matrix.fromBlocks_multiply, hQ]
  have hseam (x : A) : U x * P₀ x * V x = Q₀ x := by
    have hi : U x * P₀ x = Q₀ x * U x := by
      rw [hU]
      simp [P₀, Q₀, Matrix.fromBlocks_multiply, Matrix.sub_mul, Matrix.mul_sub,
        hP, hQ, hLp, hqL]
    rw [hi, mul_assoc, hUV, mul_one]
  have hSc : Continuous S := by
    apply continuous_matrix
    intro i j
    cases i <;> cases j
    all_goals simp only [S, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    all_goals fun_prop
  have hTc : Continuous T := by
    apply continuous_matrix
    intro i j
    cases i <;> cases j
    all_goals simp only [T, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    all_goals fun_prop
  have hS'c : Continuous S' := by
    apply continuous_matrix
    intro i j
    cases i <;> cases j
    all_goals simp only [S', Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    all_goals fun_prop
  have hT'c : Continuous T' := by
    apply continuous_matrix
    intro i j
    cases i <;> cases j
    all_goals simp only [T', Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    all_goals fun_prop
  have hUc : Continuous U := (hSc.mul hTc).mul hSc
  have hVc : Continuous V := (hS'c.mul hT'c).mul hS'c
  have hP₀c : Continuous P₀ := by
    apply continuous_matrix
    intro i j
    cases i <;> cases j
    all_goals simp only [P₀, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    all_goals fun_prop
  have hQ₀c : Continuous Q₀ := by
    apply continuous_matrix
    intro i j
    cases i <;> cases j
    all_goals simp only [Q₀, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    all_goals fun_prop
  let reindex := Matrix.reindexRingEquiv ℂ (finSumFinEquiv (m := p.size) (n := q.size))
  let Rl (x : X) := reindex (U x * P₀ x * V x)
  let Rr (x : X) := reindex (Q₀ x)
  have hRlc : Continuous Rl := by
    apply continuous_matrix
    intro i j
    exact (((hUc.mul hP₀c).mul hVc).matrix_elem _ _)
  have hRrc : Continuous Rr := by
    apply continuous_matrix
    intro i j
    exact hQ₀c.matrix_elem _ _
  have hRseam (x : A) : Rl x = Rr x := congrArg reindex (hseam x)
  have hRrel (s t : X ⊕ X) (hst : DoubleRel A s t) :
      Sum.elim Rl Rr s = Sum.elim Rl Rr t := by
    rcases hst with ⟨hb, he | ha⟩
    · rw [he]
    · cases s with
      | inl x =>
        cases t with
        | inl y => exact congrArg Rl hb
        | inr y =>
          change x = y at hb
          subst y
          exact hRseam ⟨x, ha⟩
      | inr x =>
        cases t with
        | inl y =>
          change x = y at hb
          subst y
          exact (hRseam ⟨x, ha⟩).symm
        | inr y => exact congrArg Rr hb
  let R : DoubleSpace A → Matrix (Fin (p.size + q.size)) (Fin (p.size + q.size)) ℂ :=
    Quotient.lift (Sum.elim Rl Rr) hRrel
  have hRc : Continuous R := continuous_quot_lift _ (hRlc.sumElim hRrc)
  have hRR (z : DoubleSpace A) : R z * R z = R z := by
    induction z using Quotient.inductionOn with
    | h s =>
      cases s with
      | inl x =>
        change reindex (U x * P₀ x * V x) * reindex (U x * P₀ x * V x) = _
        rw [← map_mul]
        apply congrArg reindex
        calc
          _ = U x * P₀ x * (V x * U x) * P₀ x * V x := by noncomm_ring
          _ = U x * P₀ x * V x := by
            rw [hVU, mul_one, mul_assoc (U x) (P₀ x) (P₀ x), hP₀]
      | inr x =>
        change reindex (Q₀ x) * reindex (Q₀ x) = _
        rw [← map_mul, hQ₀]
        rfl
  -- Descent of the actual continuous idempotent produces a finite-rank bundle on the double.
  let r : IdempotentMatrix C(DoubleSpace A, ℂ) :=
    { size := p.size + q.size
      matrix i j := ⟨fun z ↦ R z i j, hRc.matrix_elem i j⟩
      mul_self := by
        apply Matrix.ext
        intro i j
        apply ContinuousMap.ext
        intro z
        simp only [HMul.hMul, dotProduct, ContinuousMap.sum_apply, ContinuousMap.coe_mk]
        exact congrFun (congrFun (hRR z) i) j }
  let W : FiniteBundle (DoubleSpace A) := FiniteBundle.ofFamily (fun z ↦ r.fiber z)
  let Ml (x : X) : Matrix (Fin (p.size + q.size)) (Fin p.size) ℂ :=
    (U x * Matrix.fromRows (P x) (0 : Matrix (Fin q.size) (Fin p.size) ℂ)).submatrix
      finSumFinEquiv.symm id
  let Nl (x : X) : Matrix (Fin p.size) (Fin (p.size + q.size)) ℂ :=
    (Matrix.fromCols (P x) (0 : Matrix (Fin p.size) (Fin q.size) ℂ) * V x).submatrix
      id finSumFinEquiv.symm
  let Mr (x : X) : Matrix (Fin (p.size + q.size)) (Fin q.size) ℂ :=
    (Matrix.fromRows (0 : Matrix (Fin p.size) (Fin q.size) ℂ) (Q x)).submatrix
      finSumFinEquiv.symm id
  let Nr (x : X) : Matrix (Fin q.size) (Fin (p.size + q.size)) ℂ :=
    (Matrix.fromCols (0 : Matrix (Fin q.size) (Fin p.size) ℂ) (Q x)).submatrix
      id finSumFinEquiv.symm
  have hNlMl (x : X) : Nl x * Ml x = P x := by
    dsimp only [Nl, Ml]
    rw [Matrix.submatrix_mul_equiv]
    have hc : (Matrix.fromCols (P x) (0 : Matrix (Fin p.size) (Fin q.size) ℂ) * V x) *
        (U x * Matrix.fromRows (P x) 0) = P x := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (V x), hVU, Matrix.one_mul,
        Matrix.fromCols_mul_fromRows, hP, Matrix.zero_mul, add_zero]
    rw [hc]
    rfl
  have hMlNl (x : X) : Ml x * Nl x = (fun i j ↦ r.matrix i j (DoubleSpace.left A x)) := by
    change (U x * Matrix.fromRows (P x) (0 : Matrix (Fin q.size) (Fin p.size) ℂ)).submatrix
      finSumFinEquiv.symm id *
      (Matrix.fromCols (P x) (0 : Matrix (Fin p.size) (Fin q.size) ℂ) * V x).submatrix
        id finSumFinEquiv.symm = (U x * P₀ x * V x).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm
    erw [Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl (Fin p.size))]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.fromRows _ _),
      Matrix.fromRows_mul_fromCols, hP]
    simp [P₀, Matrix.mul_assoc]
  have hNrMr (x : X) : Nr x * Mr x = Q x := by
    dsimp only [Nr, Mr]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows,
      Matrix.zero_mul, zero_add, hQ]
    rfl
  have hMrNr (x : X) : Mr x * Nr x = (fun i j ↦ r.matrix i j (DoubleSpace.right A x)) := by
    have hm : Matrix.fromRows (0 : Matrix (Fin p.size) (Fin q.size) ℂ) (Q x) *
        Matrix.fromCols (0 : Matrix (Fin q.size) (Fin p.size) ℂ) (Q x) = Q₀ x := by
      rw [Matrix.fromRows_mul_fromCols]
      simp only [Matrix.mul_zero, Matrix.zero_mul, hQ]
      rfl
    change (Matrix.fromRows (0 : Matrix (Fin p.size) (Fin q.size) ℂ) (Q x)).submatrix
      finSumFinEquiv.symm (Equiv.refl (Fin q.size)) *
      (Matrix.fromCols (0 : Matrix (Fin q.size) (Fin p.size) ℂ) (Q x)).submatrix
        (Equiv.refl (Fin q.size)) finSumFinEquiv.symm =
          (Q₀ x).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    exact (Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl (Fin q.size)) _).trans
      (congrArg (fun t ↦ t.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) hm)
  have hrowPc : Continuous (fun x ↦
      Matrix.fromRows (P x) (0 : Matrix (Fin q.size) (Fin p.size) ℂ)) := by
    apply continuous_matrix
    intro i j
    cases i <;> simp only [Matrix.fromRows, Matrix.of_apply]
    · exact hPc.matrix_elem _ _
    · exact continuous_const
  have hrowQc : Continuous (fun x ↦
      Matrix.fromRows (0 : Matrix (Fin p.size) (Fin q.size) ℂ) (Q x)) := by
    apply continuous_matrix
    intro i j
    cases i <;> simp only [Matrix.fromRows, Matrix.of_apply]
    · exact continuous_const
    · exact hQc.matrix_elem _ _
  have hMlc : Continuous Ml := continuous_matrix (fun _ _ ↦
    (hUc.matrix_mul hrowPc).matrix_elem _ _)
  have hMrc : Continuous Mr := continuous_matrix (fun _ _ ↦ hrowQc.matrix_elem _ _)
  obtain ⟨el, hel⟩ := imageIso p r (DoubleSpace.leftMap A) Ml Nl hMlc hNlMl hMlNl
  obtain ⟨er, her⟩ := imageIso q r (DoubleSpace.rightMap A) Mr Nr hMrc hNrMr hMrNr
  have hMl (x : A) (v : p.fiber x) :
      Ml x *ᵥ v.val = (Sum.elim (0 : Fin p.size → ℂ) (d.linearEquiv x v).val) ∘
        (finSumFinEquiv (m := p.size) (n := q.size)).symm := by
    change (U x * Matrix.fromRows (P x) (0 : Matrix (Fin q.size) (Fin p.size) ℂ)).submatrix
      finSumFinEquiv.symm (Equiv.refl (Fin p.size)) *ᵥ v.val = _
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id]
    rw [← Matrix.mulVec_mulVec, Matrix.fromRows_mulVec, Matrix.zero_mulVec, hpfix, hU]
    rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, add_zero,
      Matrix.sub_mulVec, Matrix.one_mulVec, hpfix, sub_self, hL]
  have hMr (x : X) (v : q.fiber x) :
      Mr x *ᵥ v.val = (Sum.elim (0 : Fin p.size → ℂ) v.val) ∘
        (finSumFinEquiv (m := p.size) (n := q.size)).symm := by
    change (Matrix.fromRows (0 : Matrix (Fin p.size) (Fin q.size) ℂ) (Q x)).submatrix
      finSumFinEquiv.symm (Equiv.refl (Fin q.size)) *ᵥ v.val = _
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id,
      Matrix.fromRows_mulVec, Matrix.zero_mulVec, hqfix]
  let eL : Iso ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ W.Fiber)
      a.source.Fiber := (ep.trans el).symm
  let eR : Iso ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ W.Fiber)
      a.target.Fiber := (eq.trans er).symm
  refine ⟨W, eL, eR, ?_⟩
  intro x v
  -- Fiber transport across the seam retains the same ambient coordinate vector.
  have hcast (y z : DoubleSpace A) (h : y = z) (w : r.fiber y) :
      (cast (congrArg (fun t ↦ (r.fiber t : Type)) h) w).val = w.val := by
    cases h
    rfl
  change ((eq.trans er).linearEquiv x).symm
    (cast (congrArg (fun z ↦ (r.fiber z : Type)) (DoubleSpace.left_eq_right A x))
      ((ep.trans el).linearEquiv x v)) = a.boundary.linearEquiv x v
  apply ((eq.trans er).linearEquiv x).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change (cast (congrArg (fun z ↦ (r.fiber z : Type)) (DoubleSpace.left_eq_right A x))
    (el.linearEquiv x (ep.linearEquiv x v))).val =
      (er.linearEquiv x (eq.linearEquiv x (a.boundary.linearEquiv x v))).val
  have hd : d.linearEquiv x (ep.linearEquiv x v) =
      eq.linearEquiv x (a.boundary.linearEquiv x v) := by
    change eq.linearEquiv x (a.boundary.linearEquiv x
      ((ep.linearEquiv x).symm (ep.linearEquiv x v))) = _
    rw [LinearEquiv.symm_apply_apply]
  calc
    _ = (el.linearEquiv x (ep.linearEquiv x v)).val :=
      hcast (DoubleSpace.left A x) (DoubleSpace.right A x)
        (DoubleSpace.left_eq_right A x) (el.linearEquiv x (ep.linearEquiv x v))
    _ = Ml x *ᵥ (ep.linearEquiv x v).val := hel x _
    _ = (Sum.elim (0 : Fin p.size → ℂ) (d.linearEquiv x (ep.linearEquiv x v)).val) ∘
        (finSumFinEquiv (m := p.size) (n := q.size)).symm := hMl x _
    _ = (Sum.elim (0 : Fin p.size → ℂ)
        (eq.linearEquiv x (a.boundary.linearEquiv x v)).val) ∘
        (finSumFinEquiv (m := p.size) (n := q.size)).symm := by rw [hd]
    _ = Mr x *ᵥ (eq.linearEquiv x (a.boundary.linearEquiv x v)).val := (hMr x _).symm
    _ = _ := (her x _).symm

/-- Choose the bundle from the fully specified gluing existence statement. -/
def clutchingBundle (hA : IsClosed A) (a : BundleTriple A) : FiniteBundle (DoubleSpace A) :=
  (exists_clutchingBundle hA a).choose

/-- The left restriction chart belonging to the same gluing witness. -/
def clutchingLeftIso (hA : IsClosed A) (a : BundleTriple A) :
    Iso ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ (clutchingBundle hA a).Fiber)
      a.source.Fiber :=
  (exists_clutchingBundle hA a).choose_spec.choose

/-- The right restriction chart belonging to the same gluing witness. -/
def clutchingRightIso (hA : IsClosed A) (a : BundleTriple A) :
    Iso ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ (clutchingBundle hA a).Fiber)
      a.target.Fiber :=
  (exists_clutchingBundle hA a).choose_spec.choose_spec.choose

set_option backward.isDefEq.respectTransparency false in
/-- The chosen charts satisfy the original seam equation. -/
theorem clutching_compatible (hA : IsClosed A) (a : BundleTriple A) :
    ClutchingCompatible a (clutchingBundle hA a)
      (clutchingLeftIso hA a) (clutchingRightIso hA a) := by
  -- All three chosen objects are projections of one existence witness.
  exact (exists_clutchingBundle hA a).choose_spec.choose_spec.choose_spec

set_option backward.isDefEq.respectTransparency false in
/-- Crossing from the left chart to the right applies the boundary isomorphism. -/
theorem clutching_seam_apply (hA : IsClosed A) (a : BundleTriple A)
    (x : A) (v : a.source.Fiber x) :
    (clutchingRightIso hA a).linearEquiv x
      (cast (congrArg (clutchingBundle hA a).Fiber (DoubleSpace.left_eq_right A x))
        (((clutchingLeftIso hA a).linearEquiv x).symm v)) = a.boundary.linearEquiv x v := by
  -- Evaluate that same witness equation at the original boundary vector.
  exact clutching_compatible hA a x v

set_option backward.isDefEq.respectTransparency false in
/-- A bundle with the same charts and seam equation is isomorphic to the glued bundle. -/
theorem nonempty_clutching_iso (hA : IsClosed A) (a : BundleTriple A)
    (W : FiniteBundle (DoubleSpace A))
    (eL : Iso ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ W.Fiber) a.source.Fiber)
    (eR : Iso ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ W.Fiber) a.target.Fiber)
    (h : ClutchingCompatible a W eL eR) : Nonempty (Iso W.Fiber (clutchingBundle hA a).Fiber) := by
  -- Glue the actual two chart comparisons across the finite closed total-space cover.
  have glueSides
      (W V : FiniteBundle (DoubleSpace A))
      (L : Iso ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ W.Fiber)
        ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ V.Fiber))
      (R : Iso ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ W.Fiber)
        ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ V.Fiber))
      (hseam : ∀ x : A, HEq (L.linearEquiv x.val) (R.linearEquiv x.val)) :
      Nonempty (Iso W.Fiber V.Fiber) := by
    classical
    let move {z w : DoubleSpace A} (h : z = w) (e : W.Fiber z ≃ₗ[ℂ] V.Fiber z) :
        W.Fiber w ≃ₗ[ℂ] V.Fiber w := h ▸ e
    have hmove {z w : DoubleSpace A} (h : z = w) (e : W.Fiber z ≃ₗ[ℂ] V.Fiber z) :
        HEq (move h e) e := by
      cases h
      rfl
    have hright (z : DoubleSpace A) (h : DoubleSpace.left A (DoubleSpace.proj A z) ≠ z) :
        DoubleSpace.right A (DoubleSpace.proj A z) = z := by
      induction z using Quotient.inductionOn with
      | h s =>
        cases s with
        | inl x => exact (h rfl).elim
        | inr x => rfl
    -- Choose only a side of the same base point; seam compatibility removes that choice.
    let e (z : DoubleSpace A) : W.Fiber z ≃ₗ[ℂ] V.Fiber z :=
      if h : DoubleSpace.left A (DoubleSpace.proj A z) = z then
        move h (L.linearEquiv (DoubleSpace.proj A z))
      else move (hright z h) (R.linearEquiv (DoubleSpace.proj A z))
    have heL (x : X) : e (DoubleSpace.left A x) = L.linearEquiv x := by
      simp only [e, DoubleSpace.proj_left]
      rfl
    have heR (x : X) : e (DoubleSpace.right A x) = R.linearEquiv x := by
      dsimp only [e, DoubleSpace.proj_right]
      split_ifs with h
      · have hx : x ∈ A := ((DoubleSpace.left_eq_right_iff A x x).mp h).2
        exact eq_of_heq ((hmove h (L.linearEquiv x)).trans (hseam ⟨x, hx⟩))
      · rfl
    -- A closed side remains a closed embedded side on every actual bundle total space.
    have hlift (K : FiniteBundle (DoubleSpace A)) (f : C(X, DoubleSpace A))
        (hf : IsClosedEmbedding f) :
        IsClosedEmbedding (Pullback.lift (F := Unit) (E := K.Fiber) f) := by
      let j : TotalSpace Unit ((f : X → DoubleSpace A) *ᵖ K.Fiber) →
          X × TotalSpace Unit K.Fiber := pullbackTotalSpaceEmbedding f
      have hj : IsEmbedding j := by
        refine ⟨inducing_pullbackTotalSpaceEmbedding Unit K.Fiber f, ?_⟩
        rintro ⟨x, v⟩ ⟨y, w⟩ h
        have hxy : x = y := congrArg Prod.fst h
        subst y
        have hvw : v = w := TotalSpace.mk_injective (f x) (congrArg Prod.snd h)
        subst w
        rfl
      let graph : TotalSpace Unit K.Fiber → DoubleSpace A × TotalSpace Unit K.Fiber :=
        fun z ↦ (z.proj, z)
      have hgraph : Continuous graph := (continuous_proj (E := K.Fiber)).prodMk continuous_id
      have hcomp : IsEmbedding (graph ∘ Pullback.lift (F := Unit) (E := K.Fiber) f) :=
        (hf.isEmbedding.prodMap IsEmbedding.id).comp hj
      have hemb : IsEmbedding (Pullback.lift (F := Unit) (E := K.Fiber) f) :=
        IsEmbedding.of_comp (Pullback.continuous_lift Unit K.Fiber f) hgraph hcomp
      have hrange : Set.range (Pullback.lift (F := Unit) (E := K.Fiber) f) =
          (π Unit K.Fiber) ⁻¹' Set.range f := by
        ext ⟨y, v⟩
        constructor
        · rintro ⟨⟨x, w⟩, h⟩
          exact ⟨x, congrArg (π Unit K.Fiber) h⟩
        · rintro ⟨x, h⟩
          change f x = y at h
          subst y
          exact ⟨⟨x, v⟩, rfl⟩
      exact ⟨hemb, hrange ▸ hf.isClosed_range.preimage (continuous_proj (E := K.Fiber))⟩
    -- Continuity is tested after the two closed total-space inclusions, which jointly cover.
    have hcontinuous (K H : FiniteBundle (DoubleSpace A))
        (f : ∀ z, K.Fiber z → H.Fiber z)
        (hleft : Continuous (fun z : TotalSpace Unit
          ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ K.Fiber) ↦
            (⟨DoubleSpace.left A z.proj, f (DoubleSpace.left A z.proj) z.snd⟩ :
              TotalSpace Unit H.Fiber)))
        (hright : Continuous (fun z : TotalSpace Unit
          ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ K.Fiber) ↦
            (⟨DoubleSpace.right A z.proj, f (DoubleSpace.right A z.proj) z.snd⟩ :
              TotalSpace Unit H.Fiber))) :
        Continuous (fun z : TotalSpace Unit K.Fiber ↦
          (⟨z.proj, f z.proj z.snd⟩ : TotalSpace Unit H.Fiber)) := by
      let l := Pullback.lift (F := Unit) (E := K.Fiber) (DoubleSpace.leftMap A)
      let r := Pullback.lift (F := Unit) (E := K.Fiber) (DoubleSpace.rightMap A)
      have hl := hlift K (DoubleSpace.leftMap A) (DoubleSpace.isClosedEmbedding_left A hA)
      have hr := hlift K (DoubleSpace.rightMap A) (DoubleSpace.isClosedEmbedding_right A hA)
      have hL : ContinuousOn (fun z : TotalSpace Unit K.Fiber ↦
          (⟨z.proj, f z.proj z.snd⟩ : TotalSpace Unit H.Fiber)) (Set.range l) := by
        rw [← Set.image_univ]
        exact hl.isEmbedding.isInducing.continuousOn_image_iff.mpr hleft.continuousOn
      have hR : ContinuousOn (fun z : TotalSpace Unit K.Fiber ↦
          (⟨z.proj, f z.proj z.snd⟩ : TotalSpace Unit H.Fiber)) (Set.range r) := by
        rw [← Set.image_univ]
        exact hr.isEmbedding.isInducing.continuousOn_image_iff.mpr hright.continuousOn
      have hcover : Set.range l ∪ Set.range r = Set.univ := by
        apply Set.eq_univ_of_forall
        rintro ⟨z, v⟩
        induction z using Quotient.inductionOn with
        | h s =>
          cases s with
          | inl x => exact Or.inl ⟨⟨x, v⟩, rfl⟩
          | inr x => exact Or.inr ⟨⟨x, v⟩, rfl⟩
      rw [← continuousOn_univ, ← hcover]
      exact hL.union_of_isClosed hR hl.isClosed_range hr.isClosed_range
    refine ⟨{ linearEquiv := e, continuous_total := ?_, continuous_symm := ?_ }⟩
    · apply hcontinuous W V (fun z ↦ e z)
      · convert (Pullback.continuous_lift Unit V.Fiber
          (DoubleSpace.leftMap A)).comp L.continuous_total using 1
        funext z
        change (⟨DoubleSpace.left A z.proj, e (DoubleSpace.left A z.proj) z.snd⟩ :
          TotalSpace Unit V.Fiber) = ⟨_, L.linearEquiv z.proj z.snd⟩
        rw [heL]
        rfl
      · convert (Pullback.continuous_lift Unit V.Fiber
          (DoubleSpace.rightMap A)).comp R.continuous_total using 1
        funext z
        change (⟨DoubleSpace.right A z.proj, e (DoubleSpace.right A z.proj) z.snd⟩ :
          TotalSpace Unit V.Fiber) = ⟨_, R.linearEquiv z.proj z.snd⟩
        rw [heR]
        rfl
    · apply hcontinuous V W (fun z ↦ (e z).symm)
      · convert (Pullback.continuous_lift Unit W.Fiber
          (DoubleSpace.leftMap A)).comp L.continuous_symm using 1
        funext z
        change (⟨DoubleSpace.left A z.proj, (e (DoubleSpace.left A z.proj)).symm z.snd⟩ :
          TotalSpace Unit W.Fiber) = ⟨_, (L.linearEquiv z.proj).symm z.snd⟩
        rw [heL]
        rfl
      · convert (Pullback.continuous_lift Unit W.Fiber
          (DoubleSpace.rightMap A)).comp R.continuous_symm using 1
        funext z
        change (⟨DoubleSpace.right A z.proj, (e (DoubleSpace.right A z.proj)).symm z.snd⟩ :
          TotalSpace Unit W.Fiber) = ⟨_, (R.linearEquiv z.proj).symm z.snd⟩
        rw [heR]
        rfl
  let V := clutchingBundle hA a
  let dL := clutchingLeftIso hA a
  let dR := clutchingRightIso hA a
  have hV : ClutchingCompatible a V dL dR := clutching_compatible hA a
  have hW := h
  let L := eL.trans dL.symm
  let R := eR.trans dR.symm
  apply glueSides W V L R
  intro x
  let h := DoubleSpace.left_eq_right A x
  have hCW (v : W.Fiber (DoubleSpace.left A x)) :
      eR.linearEquiv x (cast (congrArg W.Fiber h) v) =
        a.boundary.linearEquiv x (eL.linearEquiv x v) := by
    simpa only [LinearEquiv.symm_apply_apply] using hW x (eL.linearEquiv x v)
  have hCV (v : V.Fiber (DoubleSpace.left A x)) :
      dR.linearEquiv x (cast (congrArg V.Fiber h) v) =
        a.boundary.linearEquiv x (dL.linearEquiv x v) := by
    calc
      _ = dR.linearEquiv x (cast (congrArg V.Fiber h)
          ((dL.linearEquiv x).symm (dL.linearEquiv x v))) :=
        congrArg (fun w : V.Fiber (DoubleSpace.left A x) ↦
          dR.linearEquiv x (cast (congrArg V.Fiber h) w))
            ((dL.linearEquiv x).symm_apply_apply v).symm
      _ = _ := hV x (dL.linearEquiv x v)
  have heq (v : W.Fiber (DoubleSpace.left A x)) :
      cast (congrArg V.Fiber h) (L.linearEquiv x v) =
        R.linearEquiv x (cast (congrArg W.Fiber h) v) := by
    apply (dR.linearEquiv x).injective
    rw [hCV]
    change a.boundary.linearEquiv x
      (dL.linearEquiv x ((dL.linearEquiv x).symm (eL.linearEquiv x v))) =
        dR.linearEquiv x ((dR.linearEquiv x).symm
          (eR.linearEquiv x (cast (congrArg W.Fiber h) v)))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hCW]
  have htransport {z w : DoubleSpace A} (hz : z = w)
      (f : W.Fiber z ≃ₗ[ℂ] V.Fiber z) (g : W.Fiber w ≃ₗ[ℂ] V.Fiber w)
      (hfg : ∀ v, cast (congrArg V.Fiber hz) (f v) =
        g (cast (congrArg W.Fiber hz) v)) : HEq f g := by
    cases hz
    exact heq_of_eq (LinearEquiv.ext hfg)
  exact htransport h _ _ heq


set_option backward.isDefEq.respectTransparency false in
/-- Isomorphic triples have isomorphic glued bundles. -/
theorem nonempty_clutching_iso_of_isIsomorphic (hA : IsClosed A) (a b : BundleTriple A)
    (h : a.IsIsomorphic b) :
    Nonempty (Iso (clutchingBundle hA a).Fiber (clutchingBundle hA b).Fiber) := by
  obtain ⟨u, v, huv⟩ := h
  let eL := (clutchingLeftIso hA a).trans u
  let eR := (clutchingRightIso hA a).trans v
  apply nonempty_clutching_iso hA b (clutchingBundle hA a) eL eR
  intro x w
  change v.linearEquiv x ((clutchingRightIso hA a).linearEquiv x
    (cast (congrArg (clutchingBundle hA a).Fiber (DoubleSpace.left_eq_right A x))
      (((clutchingLeftIso hA a).linearEquiv x).symm ((u.linearEquiv x).symm w)))) =
        b.boundary.linearEquiv x w
  rw [clutching_seam_apply, huv, LinearEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Clutching a direct sum agrees with direct sum of the glued bundles. -/
theorem nonempty_clutching_sum_iso (hA : IsClosed A) (a b : BundleTriple A) :
    Nonempty (Iso (clutchingBundle hA (a.sum b)).Fiber
      ((clutchingBundle hA a).sum (clutchingBundle hA b)).Fiber) := by
  let Wa := clutchingBundle hA a
  let Wb := clutchingBundle hA b
  -- The original pullback and sum topologies identify by the identity on fiber pairs.
  let compare (f : C(X, DoubleSpace A)) :
      Iso (((Wa.sum Wb).pullback f).Fiber)
        (((Wa.pullback f).sum (Wb.pullback f)).Fiber) :=
    { linearEquiv y := LinearEquiv.refl ℂ (Wa.Fiber (f y) × Wb.Fiber (f y))
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply Continuous.prodMk
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit Wa.Fiber f).continuous_iff]
          exact (Pullback.continuous_proj Unit (Wa.sum Wb).Fiber f).prodMk
            (continuous_sum_fst.comp (Pullback.continuous_lift Unit (Wa.sum Wb).Fiber f))
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit Wb.Fiber f).continuous_iff]
          exact (Pullback.continuous_proj Unit (Wa.sum Wb).Fiber f).prodMk
            (continuous_sum_snd.comp (Pullback.continuous_lift Unit (Wa.sum Wb).Fiber f))
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (Wa.sum Wb).Fiber f).continuous_iff]
        apply ((Pullback.continuous_proj Unit Wa.Fiber f).comp continuous_sum_fst).prodMk
        apply continuous_induced_rng.mpr
        exact ((Pullback.continuous_lift Unit Wa.Fiber f).comp continuous_sum_fst).prodMk
          ((Pullback.continuous_lift Unit Wb.Fiber f).comp continuous_sum_snd) }
  let eL := (compare (DoubleSpace.leftMap A)).trans
    ((clutchingLeftIso hA a).sum (clutchingLeftIso hA b))
  let eR := (compare (DoubleSpace.rightMap A)).trans
    ((clutchingRightIso hA a).sum (clutchingRightIso hA b))
  have hcast {z w : DoubleSpace A} (h : z = w) (v : Wa.Fiber z) (u : Wb.Fiber z) :
      cast (congrArg (Wa.sum Wb).Fiber h) (v, u) =
        (cast (congrArg Wa.Fiber h) v, cast (congrArg Wb.Fiber h) u) := by
    cases h
    rfl
  have hc : ClutchingCompatible (a.sum b) (Wa.sum Wb) eL eR := by
    intro x v
    change ((clutchingRightIso hA a).linearEquiv x
        (cast (congrArg (Wa.sum Wb).Fiber (DoubleSpace.left_eq_right A x))
          (((clutchingLeftIso hA a).linearEquiv x).symm v.1,
            ((clutchingLeftIso hA b).linearEquiv x).symm v.2)).1,
      (clutchingRightIso hA b).linearEquiv x
        (cast (congrArg (Wa.sum Wb).Fiber (DoubleSpace.left_eq_right A x))
          (((clutchingLeftIso hA a).linearEquiv x).symm v.1,
            ((clutchingLeftIso hA b).linearEquiv x).symm v.2)).2) =
      (RelativeTriple.sum a.boundary b.boundary).linearEquiv x v
    rw [hcast (DoubleSpace.left_eq_right A x), RelativeTriple.sum_apply]
    exact Prod.ext (clutching_seam_apply hA a x v.1) (clutching_seam_apply hA b x v.2)
  obtain ⟨e⟩ := nonempty_clutching_iso hA (a.sum b) (Wa.sum Wb) eL eR hc
  exact ⟨e.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Gluing an identity triple yields projection pullback of its bundle. -/
theorem nonempty_clutching_identity_iso (hA : IsClosed A) (E : FiniteBundle X) :
    Nonempty (Iso (clutchingBundle hA (BundleTriple.identity A E)).Fiber
      (E.pullback (DoubleSpace.projMap A)).Fiber) := by
  let W := E.pullback (DoubleSpace.projMap A)
  let eL : Iso ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ W.Fiber) E.Fiber :=
    (pullbackCompIso (E := E.Fiber) (DoubleSpace.projMap A)
      (DoubleSpace.leftMap A)).trans (pullbackIdIso (E := E.Fiber))
  let eR : Iso ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ W.Fiber) E.Fiber :=
    (pullbackCompIso (E := E.Fiber) (DoubleSpace.projMap A)
      (DoubleSpace.rightMap A)).trans (pullbackIdIso (E := E.Fiber))
  have heL (x : X) (v : E.Fiber x) : eL.linearEquiv x v = v := by
    change (pullbackIdIso (E := E.Fiber)).linearEquiv x
      ((pullbackCompIso (E := E.Fiber) (DoubleSpace.projMap A)
        (DoubleSpace.leftMap A)).linearEquiv x v) = v
    rw [pullbackIdIso_apply, pullbackCompIso_apply]
  have heR (x : X) (v : E.Fiber x) : eR.linearEquiv x v = v := by
    change (pullbackIdIso (E := E.Fiber)).linearEquiv x
      ((pullbackCompIso (E := E.Fiber) (DoubleSpace.projMap A)
        (DoubleSpace.rightMap A)).linearEquiv x v) = v
    rw [pullbackIdIso_apply, pullbackCompIso_apply]
  have hinv (x : X) (v : E.Fiber x) : (eL.linearEquiv x).symm v = v := by
    apply (eL.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, heL]
  have hc : ClutchingCompatible (BundleTriple.identity A E) W eL eR := by
    intro x v
    change eR.linearEquiv x
      (cast (congrArg W.Fiber (DoubleSpace.left_eq_right A x)) ((eL.linearEquiv x).symm v)) = v
    rw [heR, hinv]
    rfl
  obtain ⟨e⟩ := nonempty_clutching_iso hA (BundleTriple.identity A E) W eL eR hc
  exact ⟨e.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Clutching commutes with the specified inverse-image pullback. -/
theorem nonempty_clutching_pullback_iso {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] (hA : IsClosed A) (a : BundleTriple A) (f : C(Y, X)) :
    Nonempty (Iso (clutchingBundle (hA.preimage f.continuous) (a.pullback f)).Fiber
      ((clutchingBundle hA a).pullback
        (DoubleSpace.mapContinuous (f ⁻¹' A) A f (fun _ hx ↦ hx))).Fiber) := by
  let Wa := clutchingBundle hA a
  let fd := DoubleSpace.mapContinuous (f ⁻¹' A) A f (fun _ hx ↦ hx)
  let W := Wa.pullback fd
  -- Both routes preserve the original fiber, with the same map of the double.
  let uL : Iso ((DoubleSpace.leftMap (f ⁻¹' A) : Y → DoubleSpace (f ⁻¹' A)) *ᵖ W.Fiber)
      ((f : Y → X) *ᵖ ((DoubleSpace.leftMap A : X → DoubleSpace A) *ᵖ Wa.Fiber)) :=
    (pullbackCompIso (E := Wa.Fiber) fd (DoubleSpace.leftMap (f ⁻¹' A))).trans
      (pullbackCompIso (E := Wa.Fiber) (DoubleSpace.leftMap A) f).symm
  let uR : Iso ((DoubleSpace.rightMap (f ⁻¹' A) : Y → DoubleSpace (f ⁻¹' A)) *ᵖ W.Fiber)
      ((f : Y → X) *ᵖ ((DoubleSpace.rightMap A : X → DoubleSpace A) *ᵖ Wa.Fiber)) :=
    (pullbackCompIso (E := Wa.Fiber) fd (DoubleSpace.rightMap (f ⁻¹' A))).trans
      (pullbackCompIso (E := Wa.Fiber) (DoubleSpace.rightMap A) f).symm
  have huL (y : Y) (v : Wa.Fiber (DoubleSpace.left A (f y))) :
      uL.linearEquiv y v = v := by
    change ((pullbackCompIso (E := Wa.Fiber) (DoubleSpace.leftMap A) f).linearEquiv y).symm
      ((pullbackCompIso (E := Wa.Fiber) fd
        (DoubleSpace.leftMap (f ⁻¹' A))).linearEquiv y v) = v
    apply ((pullbackCompIso (E := Wa.Fiber) (DoubleSpace.leftMap A) f).linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have huR (y : Y) (v : Wa.Fiber (DoubleSpace.right A (f y))) :
      uR.linearEquiv y v = v := by
    change ((pullbackCompIso (E := Wa.Fiber) (DoubleSpace.rightMap A) f).linearEquiv y).symm
      ((pullbackCompIso (E := Wa.Fiber) fd
        (DoubleSpace.rightMap (f ⁻¹' A))).linearEquiv y v) = v
    apply ((pullbackCompIso (E := Wa.Fiber) (DoubleSpace.rightMap A) f).linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  let eL := uL.trans ((clutchingLeftIso hA a).pullback f)
  let eR := uR.trans ((clutchingRightIso hA a).pullback f)
  have heL (y : Y) (v : Wa.Fiber (DoubleSpace.left A (f y))) :
      eL.linearEquiv y v = (clutchingLeftIso hA a).linearEquiv (f y) v := by
    change (clutchingLeftIso hA a).linearEquiv (f y) (uL.linearEquiv y v) = _
    rw [huL]
  have heR (y : Y) (v : Wa.Fiber (DoubleSpace.right A (f y))) :
      eR.linearEquiv y v = (clutchingRightIso hA a).linearEquiv (f y) v := by
    change (clutchingRightIso hA a).linearEquiv (f y) (uR.linearEquiv y v) = _
    rw [huR]
  have hinv (y : Y) (v : a.source.Fiber (f y)) :
      (eL.linearEquiv y).symm v = ((clutchingLeftIso hA a).linearEquiv (f y)).symm v := by
    apply (eL.linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply, heL, LinearEquiv.apply_symm_apply]
  have hc : ClutchingCompatible (a.pullback f) W eL eR := by
    intro y v
    change eR.linearEquiv y
      (cast (congrArg W.Fiber (DoubleSpace.left_eq_right (f ⁻¹' A) y))
        ((eL.linearEquiv y).symm v)) = (a.boundary.pullback f).linearEquiv y v
    rw [heR, hinv, RelativeTriple.pullback_apply]
    exact clutching_seam_apply hA a ⟨f y, y.property⟩ v
  obtain ⟨e⟩ := nonempty_clutching_iso (hA.preimage f.continuous) (a.pullback f) W eL eR hc
  exact ⟨e.symm⟩

end AtiyahSinger.ComplexBundle
