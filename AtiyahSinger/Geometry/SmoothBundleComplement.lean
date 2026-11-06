/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth complements over compact manifolds

Public module ID: M1371.

K01: the smooth fixed-rank finite complement theorem over a compact
Hausdorff second-countable smooth manifold. The given bundle and its atlas
are retained. The conclusion supplies an actual smooth
bundle and a fiberwise linear equivalence with a finite trivial bundle.
Smoothness of the equivalence and its inverse is expressed through their two
blocks, using the original factor atlases and the standard trivial atlas.
These four conditions are exactly smoothness of the direct-sum isomorphism;
they do not require a newly chosen atlas on the original bundle.

Source: Spin Geometry I.9, Lemma 9.8 and Corollary 9.9. Their finite partition-of-unity
embedding and orthogonal-complement argument gives the standard existence
result. Here a smooth partition of unity yields a split weighted embedding,
and explicit quotient coordinates realize its algebraic complement.
The conclusion is fixed-rank and complex-linear. The real manifold
model has no boundary; rank zero and the empty base are allowed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothFiniteComplexBundle

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hS : SecondCountableTopology M] [hC : CompactSpace M]

include hM hT hS hC

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in

/-- Every smooth finite-rank complex bundle on a compact Hausdorff second-countable
smooth manifold has a smooth complement.
The same fiber equivalence occurs in all four smoothness assertions. -/
theorem exists_smooth_complement (E : SmoothFiniteComplexBundle (n := n) M) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M,
      ∃ e : ∀ x : M, (E.Fiber x × F.Fiber x) ≃ₗ[ℂ]
          EuclideanSpace ℂ (Fin (E.rank + F.rank)),
        IsSmoothBundleMap (n := n) (r := E.rank) (q := E.rank + F.rank)
          (E := E.Fiber)
          (F := Bundle.Trivial M (EuclideanSpace ℂ (Fin (E.rank + F.rank))))
          (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E.Fiber x) (F.Fiber x))) ∧
        IsSmoothBundleMap (n := n) (r := F.rank) (q := E.rank + F.rank)
          (E := F.Fiber)
          (F := Bundle.Trivial M (EuclideanSpace ℂ (Fin (E.rank + F.rank))))
          (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E.Fiber x) (F.Fiber x))) ∧
        IsSmoothBundleMap (n := n) (r := E.rank + F.rank) (q := E.rank)
          (E := Bundle.Trivial M (EuclideanSpace ℂ (Fin (E.rank + F.rank))))
          (F := E.Fiber)
          (fun x ↦ (LinearMap.fst ℂ (E.Fiber x) (F.Fiber x)).comp
            (e x).symm.toLinearMap) ∧
        IsSmoothBundleMap (n := n) (r := E.rank + F.rank) (q := F.rank)
          (E := Bundle.Trivial M (EuclideanSpace ℂ (Fin (E.rank + F.rank))))
          (F := F.Fiber)
          (fun x ↦ (LinearMap.snd ℂ (E.Fiber x) (F.Fiber x)).comp
            (e x).symm.toLinearMap) := by
  /- Stage 1: choose finitely many original smooth frames and subordinate smooth
  partition functions. Their weighted coordinate maps extend smoothly by zero.
  The combined map J embeds E into a finite trivial bundle because some weight
  is nonzero at every point. The empty base is treated separately.
  Stage 2: the positive sum of squared weights normalizes a smooth left inverse
  R of J. Thus Q = id - J R projects onto ker R. On each nonzero-weight open
  set, subtract the embedded vector determined by that block and delete it.
  These quotient coordinates have a common finite dimension; their smooth
  transition maps construct F and identify its fibers with ker R through Q.
  Stage 3: add the embedded E vector to the representative in ker R. The
  inverse uses R and the same quotient coordinate maps. Reindex the finite
  target by Fin (E.rank + F.rank), then verify the two inclusions and two
  inverse projections in the supplied atlases. All four maps use this same
  equivalence and retain the original E atlas; rank zero is included. -/

  classical
  cases isEmpty_or_nonempty M with
  | inl hEmpty =>
    -- An empty base requires no choice of a point or of a fiber coordinate.
    let := hEmpty
    let F : SmoothFiniteComplexBundle (n := n) M :=
      { rank := 0
        Fiber := Bundle.Trivial M (EuclideanSpace ℂ (Fin 0))
        isSmooth := ⟨by
          intro d f hd hf x hx
          exact isEmptyElim x⟩ }
    refine ⟨F, (fun x ↦ isEmptyElim x), ?_, ?_, ?_, ?_⟩
    all_goals
      intro d hd f hf j x hx
      exact isEmptyElim x
  | inr hNonempty =>
    let := hNonempty
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let H := EuclideanSpace ℂ (Fin E.rank)
    -- Retain the original countability input in the smooth partition construction.
    let : SigmaCompactSpace M :=
      @sigmaCompactSpace_of_locallyCompact_secondCountable M _ inferInstance hS
    -- Fix finitely many original frames; the extra frame makes the index a successor.
    let d (x : M) := trivializationAt H E.Fiber x
    let U (x : M) := (d x).baseSet
    have hopen (x : M) : IsOpen (U x) := (d x).open_baseSet
    have hcover : Set.univ ⊆ ⋃ x, U x := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨x, mem_baseSet_trivializationAt H E.Fiber x⟩
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
    let k := s.card
    let f : Fin k ≃ s := s.equivFin.symm
    let point : Fin (k + 1) → M := Fin.cases (Classical.choice hNonempty) (fun j ↦ f j)
    let e (i : Fin (k + 1)) := d (point i)
    let O (i : Fin (k + 1)) := (e i).baseSet
    have hOcover : Set.univ ⊆ ⋃ i, O i := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
      refine Set.mem_iUnion.mpr ⟨(f.symm ⟨y, hy⟩).succ, ?_⟩
      simpa [O, e, point, U] using hxy
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ O
      (fun i ↦ (e i).open_baseSet) hOcover
    have hsum (x : M) : ∑ i : Fin (k + 1), ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
    have hnonzero (x : M) : ∃ i : Fin (k + 1), ρ i x ≠ 0 := by
      by_contra! h
      have h1 := hsum x
      simp only [h, Finset.sum_const_zero] at h1
      exact zero_ne_one h1
    let w (i : Fin (k + 1)) (x : M) : ℂ := ρ i x
    have hwzero (i : Fin (k + 1)) (x : M) (hx : x ∉ O i) : w i x = 0 := by
      have h0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρ i h))
      exact Complex.ofReal_eq_zero.mpr h0
    let S (x : M) : ℝ := ∑ i : Fin (k + 1), (ρ i x) ^ 2
    have hSpos (x : M) : 0 < S x := by
      obtain ⟨i, hi⟩ := hnonzero x
      exact Finset.sum_pos' (fun j _ ↦ sq_nonneg (ρ j x))
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    let b (x : M) : ℂ := ((S x)⁻¹ : ℝ)
    have hbnorm (x : M) : b x * ∑ i : Fin (k + 1), (w i x) ^ 2 = 1 := by
      have hs : (∑ i : Fin (k + 1), (w i x) ^ 2) = (S x : ℂ) := by
        simp [w, S]
      rw [hs]
      dsimp only [b]
      rw [Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hSpos x).ne')]
    let V := Fin (k + 1) → H
    let W := Fin k → H
    -- J is the finite weighted frame map, and R is a global smooth left inverse.
    let J (x : M) : E.Fiber x →ₗ[ℂ] V :=
      LinearMap.pi (fun i ↦ w i x • (e i).linearMapAt ℂ x)
    let R (x : M) : V →ₗ[ℂ] E.Fiber x := b x •
      ∑ i : Fin (k + 1), w i x •
        ((e i).symmL ℂ x).toLinearMap.comp (LinearMap.proj i)
    have hJi (x : M) (v : E.Fiber x) (i : Fin (k + 1)) :
        J x v i = w i x • (e i).linearMapAt ℂ x v := rfl
    have hRJ (x : M) (v : E.Fiber x) : R x (J x v) = v := by
      have hterm (i : Fin (k + 1)) :
          w i x • (e i).symmL ℂ x (J x v i) = (w i x) ^ 2 • v := by
        by_cases hx : x ∈ O i
        · rw [hJi, map_smul, (e i).coe_linearMapAt_of_mem hx, (e i).symmL_apply hx,
            (e i).symm_apply_apply_mk hx, smul_smul, pow_two]
        · rw [hwzero i x hx]
          simp
      calc
        R x (J x v) = b x • ∑ i : Fin (k + 1),
            w i x • (e i).symmL ℂ x (J x v i) := by
          simp only [R, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
          rfl
        _ = b x • ∑ i : Fin (k + 1), (w i x) ^ 2 • v := by simp_rw [hterm]
        _ = v := by rw [← Finset.sum_smul, smul_smul, hbnorm, one_smul]
    let Q (x : M) : V →ₗ[ℂ] V := LinearMap.id - (J x).comp (R x)
    have hQ (x : M) (z : V) : Q x z = z - J x (R x z) := rfl
    have hQJ (x : M) (v : E.Fiber x) : Q x (J x v) = 0 := by
      rw [hQ, hRJ, sub_self]
    have hRQ (x : M) (z : V) : R x (Q x z) = 0 := by
      rw [hQ, map_sub, hRJ, sub_self]
    -- On a nonzero-weight chart, a deleted block identifies the quotient with W.
    let A (i : Fin (k + 1)) := {x : M | ρ i x ≠ 0}
    have hAopen (i : Fin (k + 1)) : IsOpen (A i) := isOpen_ne.preimage (ρ i).contMDiff.continuous
    have hAinside (i : Fin (k + 1)) (x : M) (hx : x ∈ A i) : x ∈ O i := by
      exact hρ i (subset_tsupport (ρ i) hx)
    let idx (x : M) : Fin (k + 1) := (hnonzero x).choose
    have hidx (x : M) : x ∈ A (idx x) := (hnonzero x).choose_spec
    let ins (i : Fin (k + 1)) : W →ₗ[ℂ] V :=
      { toFun := fun v ↦ Fin.insertNth (α := fun _ ↦ H) i 0 v
        map_add' := by
          intro u v
          apply funext
          change ∀ j, Fin.insertNth (α := fun _ ↦ H) i 0 (u + v) j =
            Fin.insertNth (α := fun _ ↦ H) i 0 u j + Fin.insertNth (α := fun _ ↦ H) i 0 v j
          rw [Fin.forall_iff_succAbove i]
          constructor
          · simp
          · intro a
            simp only [Fin.insertNth_apply_succAbove]
            rfl
        map_smul' := by
          intro c v
          apply funext
          change ∀ j, Fin.insertNth (α := fun _ ↦ H) i 0 (c • v) j =
            c • Fin.insertNth (α := fun _ ↦ H) i 0 v j
          rw [Fin.forall_iff_succAbove i]
          constructor
          · simp
          · intro a
            simp only [Fin.insertNth_apply_succAbove]
            rfl }
    let drop (i : Fin (k + 1)) : V →ₗ[ℂ] W :=
      { toFun := Fin.removeNth (α := fun _ ↦ H) i
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hIns (i : Fin (k + 1)) (z : V) (hz : z i = 0) : ins i (drop i z) = z := by
      exact Fin.insertNth_eq_iff.mpr ⟨hz.symm, rfl⟩
    have hDrop (i : Fin (k + 1)) (v : W) : drop i (ins i v) = v :=
      by
        funext j
        exact Fin.insertNth_apply_succAbove (α := fun _ ↦ H) i 0 v j
    let C (i : Fin (k + 1)) (x : M) : V →ₗ[ℂ] E.Fiber x :=
      (w i x)⁻¹ • ((e i).symmL ℂ x).toLinearMap.comp (LinearMap.proj i)
    let p (i : Fin (k + 1)) (x : M) : V →ₗ[ℂ] W :=
      (drop i).comp (LinearMap.id - (J x).comp (C i x))
    have hCJi (i : Fin (k + 1)) (x : M) (hx : x ∈ A i) (v : E.Fiber x) :
        C i x (J x v) = v := by
      have hxi := hAinside i x hx
      have hw : w i x ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      change (w i x)⁻¹ • (e i).symmL ℂ x (J x v i) = v
      rw [hJi, map_smul, (e i).coe_linearMapAt_of_mem hxi, (e i).symmL_apply hxi,
        (e i).symm_apply_apply_mk hxi, smul_smul, inv_mul_cancel₀ hw, one_smul]
    have hJC (i : Fin (k + 1)) (x : M) (hx : x ∈ A i) (z : V) :
        J x (C i x z) i = z i := by
      have hxi := hAinside i x hx
      have hw : w i x ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      rw [hJi]
      change w i x • (e i).linearMapAt ℂ x
        ((w i x)⁻¹ • (e i).symmL ℂ x (z i)) = z i
      simp only [map_smul, (e i).coe_linearMapAt_of_mem hxi, (e i).symmL_apply hxi,
        (e i).apply_mk_symm hxi, smul_smul, mul_inv_cancel₀ hw, one_smul]
    have hpJ (i : Fin (k + 1)) (x : M) (hx : x ∈ A i) (v : E.Fiber x) :
        p i x (J x v) = 0 := by
      change drop i (J x v - J x (C i x (J x v))) = 0
      rw [hCJi i x hx, sub_self, map_zero]
    have hCins (i : Fin (k + 1)) (x : M) (v : W) : C i x (ins i v) = 0 := by
      change (w i x)⁻¹ • (e i).symmL ℂ x ((ins i v) i) = 0
      simp [ins]
    have hpins (i : Fin (k + 1)) (x : M) (v : W) : p i x (ins i v) = v := by
      change drop i (ins i v - J x (C i x (ins i v))) = v
      rw [hCins, map_zero, sub_zero, hDrop]
    have hinsP (i : Fin (k + 1)) (x : M) (hx : x ∈ A i) (z : V) :
        ins i (p i x z) = z - J x (C i x z) := by
      exact hIns i (z - J x (C i x z)) (by
        change z i - J x (C i x z) i = 0
        rw [hJC i x hx, sub_self])
    have hpQ (i : Fin (k + 1)) (x : M) (hx : x ∈ A i) (z : V) :
        p i x (Q x z) = p i x z := by
      rw [hQ, map_sub, hpJ i x hx, sub_zero]
    have hQinsP (i : Fin (k + 1)) (x : M) (hx : x ∈ A i) (z : V) :
        Q x (ins i (p i x z)) = Q x z := by
      rw [hinsP i x hx, map_sub, hQJ, sub_zero]
    -- Weighted transition matrices extend smoothly by zero off their frame supports.
    have hwSmooth (i : Fin (k + 1)) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (w i) :=
      Complex.ofRealCLM.contDiff.comp_contMDiff (ρ i).contMDiff
    have hSsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ S := by
      apply contMDiff_finsetSum
      intro i hi
      have hpow : ContDiff ℝ ∞ (fun y : ℝ ↦ y ^ 2) := contDiff_id.pow 2
      exact hpow.comp_contMDiff (ρ i).contMDiff
    have hbsmooth : ContMDiff I 𝓘(ℝ, ℂ) ∞ b :=
      Complex.ofRealCLM.contDiff.comp_contMDiff
        (hSsmooth.inv₀ (fun x ↦ (hSpos x).ne'))
    have hweighted (i : Fin (k + 1)) (s : Set M) (hs : IsOpen s)
        (T : M → H →L[ℂ] H)
        (hT : ContMDiffOn I 𝓘(ℝ, H →L[ℂ] H) ∞ T (s ∩ O i)) :
        ContMDiffOn I 𝓘(ℝ, H →L[ℂ] H) ∞ (fun x ↦ w i x • T x) s := by
      intro x hx
      by_cases hxs : x ∈ tsupport (ρ i)
      · have ht := hT.contMDiffAt ((hs.inter (e i).open_baseSet).mem_nhds
          ⟨hx, hρ i hxs⟩)
        have hmul : ContDiff ℝ ∞
            (fun z : ℂ × (H →L[ℂ] H) ↦ z.1 • z.2) := contDiff_smul
        exact (hmul.comp_contMDiffAt
          ((hwSmooth i).contMDiffAt.prodMk_space ht)).contMDiffWithinAt
      · apply ContMDiffAt.contMDiffWithinAt
        apply (contMDiffAt_const (c := (0 : H →L[ℂ] H))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport (ρ i)).isOpen_compl.mem_nhds hxs] with y hy
        have h0 : w i y = 0 := Complex.ofReal_eq_zero.mpr
          (image_eq_zero_of_notMem_tsupport hy)
        rw [h0]
        exact zero_smul ℂ (T y)
    let pack : (Fin (k + 1) → H →L[ℂ] H) →L[ℂ] (H →L[ℂ] V) :=
      ({ toFun := ContinuousLinearMap.pi
         map_add' := by intro u v; rfl
         map_smul' := by intro c v; rfl } :
        (Fin (k + 1) → H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] V)).toContinuousLinearMap
    let Jm (d₀ : Trivialization H (π H E.Fiber)) [MemTrivializationAtlas d₀]
        (x : M) : H →L[ℂ] V :=
      ContinuousLinearMap.pi (fun i ↦ w i x • (d₀.coordChangeL ℂ (e i) x : H →L[ℂ] H))
    have hJm (d₀ : Trivialization H (π H E.Fiber)) [MemTrivializationAtlas d₀] :
        ContMDiffOn I 𝓘(ℝ, H →L[ℂ] V) ∞ (Jm d₀) d₀.baseSet := by
      exact pack.restrictScalars ℝ |>.contMDiff.comp_contMDiffOn
        (contMDiffOn_pi_space.mpr (fun i ↦ hweighted i _ d₀.open_baseSet _
          (IsSmoothComplexBundle.contMDiffOn_coordChange d₀ (e i))))
    have hJmEval (d₀ : Trivialization H (π H E.Fiber)) [MemTrivializationAtlas d₀]
        (x : M) (hx : x ∈ d₀.baseSet) (v : H) :
        Jm d₀ x v = J x (d₀.symmL ℂ x v) := by
      funext i
      change w i x • d₀.coordChangeL ℂ (e i) x v =
        w i x • (e i).linearMapAt ℂ x (d₀.symmL ℂ x v)
      by_cases hi : x ∈ O i
      · rw [d₀.coordChangeL_apply (R := ℂ) (e i) ⟨hx, hi⟩,
          (e i).coe_linearMapAt_of_mem hi, d₀.symmL_apply hx]
      · rw [hwzero i x hi]
        simp
    let Rm (d₀ : Trivialization H (π H E.Fiber)) [MemTrivializationAtlas d₀]
        (x : M) : V →L[ℂ] H := b x •
      ∑ i : Fin (k + 1), (w i x • (e i).coordChangeL ℂ d₀ x : H →L[ℂ] H).comp
        (ContinuousLinearMap.proj i)
    have hRm (d₀ : Trivialization H (π H E.Fiber)) [MemTrivializationAtlas d₀] :
        ContMDiffOn I 𝓘(ℝ, V →L[ℂ] H) ∞ (Rm d₀) d₀.baseSet := by
      have hsum : ContMDiffOn I 𝓘(ℝ, V →L[ℂ] H) ∞
          (fun x ↦ ∑ i : Fin (k + 1),
            (w i x • (e i).coordChangeL ℂ d₀ x : H →L[ℂ] H).comp
              (ContinuousLinearMap.proj i)) d₀.baseSet := by
        apply contMDiffOn_finsetSum
        intro i hi
        let B := ((ContinuousLinearMap.compL ℂ V H H).flip
          (ContinuousLinearMap.proj i)).restrictScalars ℝ
        apply B.contMDiff.comp_contMDiffOn
        apply hweighted i _ d₀.open_baseSet
        exact (IsSmoothComplexBundle.contMDiffOn_coordChange (e i) d₀).mono
          (fun x hx ↦ hx.symm)
      have hmul : ContDiff ℝ ∞
          (fun z : ℂ × (V →L[ℂ] H) ↦ z.1 • z.2) := contDiff_smul
      exact hmul.contMDiff.comp_contMDiffOn (hbsmooth.contMDiffOn.prodMk_space hsum)
    have hRmEval (d₀ : Trivialization H (π H E.Fiber)) [MemTrivializationAtlas d₀]
        (x : M) (hx : x ∈ d₀.baseSet) (z : V) :
        Rm d₀ x z = d₀.linearMapAt ℂ x (R x z) := by
      simp only [Rm, R, smul_apply, sum_apply,
        ContinuousLinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
        LinearMap.comp_apply, map_smul, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      change w i x • (e i).coordChangeL ℂ d₀ x (z i) =
        w i x • d₀.linearMapAt ℂ x ((e i).symmL ℂ x (z i))
      by_cases hxi : x ∈ O i
      · rw [(e i).coordChangeL_apply (R := ℂ) d₀ ⟨hxi, hx⟩,
          d₀.coe_linearMapAt_of_mem hx, (e i).symmL_apply hxi]
      · rw [hwzero i x hxi]
        simp
    -- The projection is smooth in the ambient trivial bundle, using any original E frame.
    let Qc (x : M) : V →L[ℂ] V := (Q x).toContinuousLinearMap
    have hQsmooth : ContMDiff I 𝓘(ℝ, V →L[ℂ] V) ∞ Qc := by
      intro x
      let d₀ := d x
      have hx : x ∈ d₀.baseSet := mem_baseSet_trivializationAt H E.Fiber x
      have hcomp : ContDiff ℝ ∞
          (fun z : (H →L[ℂ] V) × (V →L[ℂ] H) ↦ z.1.comp z.2) :=
        (contDiff_fst.clm_comp contDiff_snd : ContDiff ℂ ∞ _).restrict_scalars ℝ
      have hP := hcomp.comp_contMDiffAt
        (((hJm d₀).contMDiffAt (d₀.open_baseSet.mem_nhds hx)).prodMk_space
          ((hRm d₀).contMDiffAt (d₀.open_baseSet.mem_nhds hx)))
      apply ContMDiffAt.congr_of_eventuallyEq
        ((contMDiffAt_const (c := ContinuousLinearMap.id ℂ V)).sub hP)
      filter_upwards [d₀.open_baseSet.mem_nhds hx] with y hy
      apply ContinuousLinearMap.ext
      intro z
      change Q y z = z - Jm d₀ y (Rm d₀ y z)
      rw [hQ, hJmEval d₀ y hy, hRmEval d₀ y hy,
        d₀.coe_linearMapAt_of_mem hy, d₀.symmL_apply hy,
        d₀.symm_apply_apply_mk hy]
    -- Each quotient chart is smooth on its nonzero-weight domain; no rank test is needed.
    let pc (i : Fin (k + 1)) (x : M) : V →L[ℂ] W := (p i x).toContinuousLinearMap
    have hpsmooth (i : Fin (k + 1)) :
        ContMDiffOn I 𝓘(ℝ, V →L[ℂ] W) ∞ (pc i) (A i) := by
      have hinvR : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x ↦ (ρ i x)⁻¹) (A i) :=
        (ρ i).contMDiff.contMDiffOn.inv₀ (fun x hx ↦ hx)
      have hinv : ContMDiffOn I 𝓘(ℝ, ℂ) ∞ (fun x ↦ (w i x)⁻¹) (A i) := by
        apply (Complex.ofRealCLM.contMDiff.comp_contMDiffOn hinvR).congr
        intro x hx
        exact (Complex.ofReal_inv (ρ i x)).symm
      have hmul : ContDiff ℝ ∞
          (fun z : ℂ × (V →L[ℂ] H) ↦ z.1 • z.2) := contDiff_smul
      have hc : ContMDiffOn I 𝓘(ℝ, V →L[ℂ] H) ∞
          (fun x ↦ (w i x)⁻¹ • (ContinuousLinearMap.proj i : V →L[ℂ] H)) (A i) :=
        hmul.contMDiff.comp_contMDiffOn (hinv.prodMk_space contMDiffOn_const)
      have hcomp : ContDiff ℝ ∞
          (fun z : (H →L[ℂ] V) × (V →L[ℂ] H) ↦ z.1.comp z.2) :=
        (contDiff_fst.clm_comp contDiff_snd : ContDiff ℂ ∞ _).restrict_scalars ℝ
      have hjc := hcomp.contMDiff.comp_contMDiffOn
        (((hJm (e i)).mono (fun x hx ↦ hAinside i x hx)).prodMk_space hc)
      let D := ((ContinuousLinearMap.compL ℂ V V W)
        (drop i).toContinuousLinearMap).restrictScalars ℝ
      have hl := D.contMDiff.comp_contMDiffOn
        ((contMDiffOn_const (c := ContinuousLinearMap.id ℂ V)).sub hjc)
      apply hl.congr
      intro x hx
      apply ContinuousLinearMap.ext
      intro z
      change p i x z = drop i (z - Jm (e i) x ((w i x)⁻¹ • z i))
      rw [hJmEval (e i) x (hAinside i x hx), map_smul]
      rfl
    -- The smooth quotient cocycle realizes an actual fixed-rank complement bundle.
    let q := k * E.rank
    let Model := EuclideanSpace ℂ (Fin q)
    -- Finite-dimensional reindexing uses the same models, including dimension zero.
    let cW : W ≃ₗ[ℂ] Model := LinearEquiv.ofFinrankEq W Model (by
      simp [W, Model, q, H, Module.finrank_pi_fintype])
    let cV : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (E.rank + q)) :=
      LinearEquiv.ofFinrankEq V _ (by
        simp [V, H, q, Module.finrank_pi_fintype, Nat.add_mul, Nat.add_comm])
    let a (i j : Fin (k + 1)) (x : M) : Model →L[ℂ] Model :=
      LinearMap.toContinuousLinearMap
        (cW.toLinearMap.comp ((p j x).comp ((ins i).comp cW.symm.toLinearMap)))
    have ha (i j : Fin (k + 1)) (x : M) (v : Model) :
        a i j x v = cW (p j x (ins i (cW.symm v))) := rfl
    have haSelf (i : Fin (k + 1)) (x : M) (hx : x ∈ A i) (v : Model) :
        a i i x v = v := by
      rw [ha, hpins, cW.apply_symm_apply]
    have haComp (i j l : Fin (k + 1)) (x : M) (hx : x ∈ A i ∩ A j ∩ A l)
        (v : Model) : a j l x (a i j x v) = a i l x v := by
      rw [ha, ha, cW.symm_apply_apply, hinsP j x hx.1.2,
        map_sub, hpJ l x hx.2, sub_zero, ha]
    have hAsmooth (i j : Fin (k + 1)) :
        ContMDiffOn I 𝓘(ℝ, Model →L[ℂ] Model) ∞ (a i j) (A i ∩ A j) := by
      let pre := ((ContinuousLinearMap.compL ℂ Model V W).flip
        ((ins i).comp cW.symm.toLinearMap).toContinuousLinearMap).restrictScalars ℝ
      let post := ((ContinuousLinearMap.compL ℂ Model W Model)
        cW.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
      exact (post.contMDiff.comp_contMDiffOn
        (pre.contMDiff.comp_contMDiffOn (hpsmooth j))).mono Set.inter_subset_right
    let Z : VectorBundleCore ℂ M Model (Fin (k + 1)) :=
      { baseSet := A
        isOpen_baseSet := hAopen
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
    let : IsSmoothComplexBundle (n := n) (r := q) Z.Fiber := by
      constructor
      rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
      apply (hAsmooth i j).congr
      intro x hx
      apply ContinuousLinearMap.ext
      intro v
      exact Z.localTriv_coordChange_eq i j hx v
    let F : SmoothFiniteComplexBundle (n := n) M := { rank := q, Fiber := Z.Fiber }
    -- This one equivalence and its explicit inverse supply all four required blocks.
    let ec (x : M) : (E.Fiber x × F.Fiber x) ≃ₗ[ℂ] V :=
      { toLinearMap := (J x).coprod
          ((Q x).comp ((ins (idx x)).comp cW.symm.toLinearMap))
        invFun := fun z ↦ (R x z, cW (p (idx x) x z))
        left_inv := by
          intro v
          apply Prod.ext
          · change R x (J x v.1 + Q x (ins (idx x) (cW.symm v.2))) = v.1
            rw [map_add, hRJ, hRQ, add_zero]
          · change cW (p (idx x) x
              (J x v.1 + Q x (ins (idx x) (cW.symm v.2)))) = v.2
            rw [map_add, hpJ (idx x) x (hidx x), hpQ (idx x) x (hidx x),
              zero_add, hpins]
            exact cW.apply_symm_apply (show Model from v.2)
        right_inv := by
          intro z
          change J x (R x z) + Q x (ins (idx x) (cW.symm (cW (p (idx x) x z)))) = z
          rw [cW.symm_apply_apply, hQinsP (idx x) x (hidx x), hQ]
          abel }
    let equiv (x : M) := (ec x).trans cV
    have hleft (x : M) (v : E.Fiber x) : equiv x (v, 0) = cV (J x v) := by
      change cV (J x v + Q x (ins (idx x) (cW.symm 0))) = cV (J x v)
      rw [map_zero, map_zero, map_zero, add_zero]
    have hright (i : Fin (k + 1)) (x : M) (hx : x ∈ A i) (v : Model) :
        equiv x (0, (Z.localTriv i).symmL ℂ x v) = cV (Q x (ins i (cW.symm v))) := by
      rw [Z.localTriv_symmL hx]
      change cV (J x 0 + Q x (ins (idx x) (cW.symm (a i (idx x) x v)))) = _
      rw [map_zero, zero_add, ha, cW.symm_apply_apply, hQinsP (idx x) x (hidx x)]
    have hfirst (x : M) (z : EuclideanSpace ℂ (Fin (E.rank + q))) :
        ((equiv x).symm z).1 = R x (cV.symm z) := rfl
    have hsecond (i : Fin (k + 1)) (x : M) (hx : x ∈ A i)
        (z : EuclideanSpace ℂ (Fin (E.rank + q))) :
        ((Z.localTriv i) ⟨x, ((equiv x).symm z).2⟩).2 =
          cW (p i x (cV.symm z)) := by
      change a (idx x) i x (cW (p (idx x) x (cV.symm z))) = _
      rw [ha, cW.symm_apply_apply, hinsP (idx x) x (hidx x),
        map_sub, hpJ i x hx, sub_zero]
    refine ⟨F, equiv, ?_, ?_, ?_, ?_⟩
    · -- In every original E chart, the first inclusion is precisely the weighted J matrix.
      intro d₀ hd₀ t ht col
      let := hd₀
      rcases ht with ⟨rfl⟩
      simp only [Bundle.Trivial.trivialization_baseSet, Set.inter_univ]
      let v := EuclideanSpace.single col (1 : ℂ)
      let evaluation := (ContinuousLinearMap.apply ℂ V v).restrictScalars ℝ
      have hcol := evaluation.contMDiff.comp_contMDiffOn (hJm d₀)
      have hmap := cV.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
        |>.contMDiff.comp_contMDiffOn hcol
      apply hmap.congr
      intro x hx
      change equiv x (d₀.symmL ℂ x v, 0) = cV (Jm d₀ x v)
      rw [hleft, hJmEval d₀ x hx]
    · -- In a chosen complement chart, the second inclusion is Q times the fixed insertion.
      intro f₀ hf₀ t ht col
      rcases hf₀ with ⟨i, rfl⟩
      rcases ht with ⟨rfl⟩
      simp only [Bundle.Trivial.trivialization_baseSet, Set.inter_univ]
      let v : Model := EuclideanSpace.single col (1 : ℂ)
      let z : V := ins i (cW.symm v)
      let evaluation := (ContinuousLinearMap.apply ℂ V z).restrictScalars ℝ
      have hcol := evaluation.contMDiff.comp hQsmooth
      have hmap := cV.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
        |>.contMDiff.comp hcol
      apply hmap.contMDiffOn.congr
      intro x hx
      change equiv x (0, (Z.localTriv i).symmL ℂ x v) = cV (Qc x z)
      exact hright i x hx v
    · -- The first inverse block uses the same global R and the original target atlas.
      intro t ht d₀ hd₀ col
      let := hd₀
      rcases ht with ⟨rfl⟩
      simp only [Bundle.Trivial.trivialization_baseSet, Set.univ_inter]
      let z := cV.symm (EuclideanSpace.single col (1 : ℂ))
      let evaluation := (ContinuousLinearMap.apply ℂ H z).restrictScalars ℝ
      have hcol := evaluation.contMDiff.comp_contMDiffOn (hRm d₀)
      apply hcol.congr
      intro x hx
      rw [Bundle.Trivial.symmL_trivialization]
      change (d₀ ⟨x, ((equiv x).symm (EuclideanSpace.single col 1)).1⟩).2 = Rm d₀ x z
      rw [hfirst, hRmEval d₀ x hx, d₀.coe_linearMapAt_of_mem hx]
    · -- In each complement chart, the other inverse block is the quotient projection p.
      intro t ht f₀ hf₀ col
      rcases ht with ⟨rfl⟩
      rcases hf₀ with ⟨i, rfl⟩
      simp only [Bundle.Trivial.trivialization_baseSet, Set.univ_inter]
      let z := cV.symm (EuclideanSpace.single col (1 : ℂ))
      let evaluation := (ContinuousLinearMap.apply ℂ W z).restrictScalars ℝ
      have hcol := evaluation.contMDiff.comp_contMDiffOn (hpsmooth i)
      have hmap := cW.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
        |>.contMDiff.comp_contMDiffOn hcol
      apply hmap.congr
      intro x hx
      rw [Bundle.Trivial.symmL_trivialization]
      change ((Z.localTriv i) ⟨x,
        ((equiv x).symm (EuclideanSpace.single col 1)).2⟩).2 = cW (pc i x z)
      exact hsecond i x hx _

end AtiyahSinger.SmoothFiniteComplexBundle
