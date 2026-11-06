/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FormalAdjoint
public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Analysis.HermitianMetricL2
public import AtiyahSinger.Analysis.SmoothSectionMultiplication
public import AtiyahSinger.Analysis.SupportedSectionPairing
public import AtiyahSinger.Geometry.ChartLocalization
public import AtiyahSinger.Geometry.HermitianMetricDual
public import AtiyahSinger.Geometry.OpenSections
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Formal adjoints characterized by compactly supported smooth tests

Public module ID: M0366.

D02: differential formal adjunction on a manifold that need not be compact.
The original smooth section spaces, two Hermitian metrics, and positive
smooth density determine the relation. Both test sections have specified
compact supports; their actual section pairings are used without replacing
the original integrals or choosing an L2 realization. The adjoint remains a
differential operator on all smooth sections of the same order bound.

Sources: SG III.5, (5.1)--(5.3), pp.194--195, gives the metric formal-adjoint
convention and the local integration-by-parts construction. Its closed-base
presentation is extended here to compactly supported tests by the same local
argument. The noncompact statement and its locality-based uniqueness proof
are explicit project supplements, not a separately numbered theorem quoted
from SG. No ellipticity, compact base, global integrability of arbitrary
smooth sections, or choice of self-adjoint extension is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Filter
open scoped Manifold ContDiff Topology SchwartzMap ComplexConjugate Matrix.Norms.Elementwise

set_option maxSynthPendingDepth 25

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  [MeasurableSpace M]

/-- The same-density metric adjunction identity tested on the original compactly supported
smooth sections. The quantifiers retain their particular compact support sets. -/
def IsCompactTestMetricFormalAdjoint (μ : Measure M)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E) :
    Prop :=
  ∀ (K L : Set M), IsCompact K → IsCompact L →
    ∀ (u : supportedSmoothSections (n := n) (r := r) E K)
      (v : supportedSmoothSections (n := n) (r := q) F L),
      k.sectionPairing μ (P u.val) v.val = h.sectionPairing μ u.val (Q v.val)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

namespace DifferentialOperator

omit [MeasurableSpace M] hBorel in
set_option backward.isDefEq.respectTransparency false in
/-- A scalar power vanishing to the order bound detects exactly the principal symbol. -/
theorem apply_scalar_pow {d : ℕ}
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F d)
    (φ : M → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ)
    (x : M) (hφx : φ x = 0)
    (s t : smoothSections (n := n) (r := r) E)
    (ht : ∀ y, t.val y = ((φ y) ^ d : ℂ) • s.val y) :
    (P.toLinearMap t).val x = ((-Complex.I) ^ d * (d.factorial : ℂ)) •
      P.principalSymbol x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x)
        (s.val x) := by
  classical
  -- Stage 1: vanishing scalar powers kill lower jets; only the atomic top partition survives.
  have eq_atomic {n : ℕ} (c : OrderedFinpartition n) (h : c.length = n) :
      c = OrderedFinpartition.atomic n := by
    have hsum : ∑ i, c.partSize i = c.length := by
      have hh := Fintype.card_congr c.equivSigma
      simpa [Fintype.card_sigma, h] using hh
    have hparts (i : Fin c.length) : c.partSize i = 1 := by
      have hsum' : ∑ j : Fin c.length, 1 = ∑ j, c.partSize j := by
        simpa using hsum.symm
      exact ((Finset.sum_eq_sum_iff_of_le (fun j _ ↦ c.partSize_pos j)).mp hsum' i
        (Finset.mem_univ i)).symm
    rcases c with ⟨length, partSize, hpos, emb, hmono, horder, hdisjoint, hcover⟩
    dsimp only at h hparts
    subst length
    obtain rfl : partSize = fun _ ↦ 1 := funext hparts
    have hemb : (fun i : Fin n ↦ emb i 0) = id := horder.eq_id
    apply OrderedFinpartition.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext i j
      have hj : j = 0 := Subsingleton.elim _ _
      rw [hj]
      exact congrFun hemb i
  have power_jet_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ ∞ f x) (hx : f x = 0)
      (m k : ℕ) (hk : k < m) :
      iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m) x = 0 := by
    classical
    have hcomp := iteratedFDeriv_comp
      (f := f) (g := fun t : ℝ ↦ t ^ m) (n := ∞)
      (by fun_prop) hf (show (k : ℕ∞ω) ≤ ∞ by simp)
    change iteratedFDeriv ℝ k ((fun t : ℝ ↦ t ^ m) ∘ f) x = 0
    rw [hcomp]
    simp only [FormalMultilinearSeries.taylorComp]
    apply Finset.sum_eq_zero
    intro c _
    ext v
    simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      ftaylorSeries, hx, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      iteratedDeriv_fun_pow_zero,
      ite_eq_right (Nat.ne_of_lt (lt_of_le_of_lt c.length_le hk)), zero_apply]
    simp
  have power_jet_top {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ ∞ f x) (hx : f x = 0)
      (m : ℕ) (v : Fin m → E) :
      iteratedFDeriv ℝ m (fun y ↦ (f y) ^ m) x v =
        (m.factorial : ℝ) * ∏ j, fderiv ℝ f x (v j) := by
    classical
    change iteratedFDeriv ℝ m ((fun t : ℝ ↦ t ^ m) ∘ f) x v = _
    rw [iteratedFDeriv_comp (n := ∞) (by fun_prop) hf (by simp)]
    simp only [FormalMultilinearSeries.taylorComp, _root_.sum_apply]
    rw [Finset.sum_eq_single (OrderedFinpartition.atomic m)]
    · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries, hx,
        iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_fun_pow_zero,
        OrderedFinpartition.atomic_length, ite_true]
      change (∏ i : Fin m, iteratedFDeriv ℝ 1 f x (fun _ ↦ v i)) •
        (m.factorial : ℝ) = _
      have hval (i : Fin m) : iteratedFDeriv ℝ 1 f x (fun _ ↦ v i) =
          fderiv ℝ f x (v i) := iteratedFDeriv_one_apply _
      simp only [hval, smul_eq_mul, mul_comm]
    · intro c _ hc
      have hc' : c.length < m := lt_of_le_of_ne c.length_le (fun h ↦ hc (eq_atomic c h))
      simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries, hx,
        iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_fun_pow_zero,
        ite_eq_right (Nat.ne_of_lt hc')]
      simp
    · simp
  -- Stage 2: multiplying by a changing frame vector keeps only its value at the base point.
  have power_smul_jet {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E → ℝ) (g : E → F) (x : E) (hf : ContDiffAt ℝ ∞ f x)
      (hg : ContDiffAt ℝ ∞ g x) (hx : f x = 0) (m k : ℕ) (hk : k ≤ m) :
      iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m • g y) x =
        iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m • g x) x := by
    classical
    have hpower := hf.pow m
    have hdiff := hg.sub (contDiffAt_const (c := g x))
    obtain ⟨u, hu, hxu, hfu⟩ := hpower.contDiffOn' (m := (k : ℕ∞ω)) (by simp) (by simp)
    obtain ⟨v, hv, hxv, hgv⟩ := hdiff.contDiffOn' (m := (k : ℕ∞ω)) (by simp) (by simp)
    simp only [Set.insert_eq_of_mem (Set.mem_univ x), Set.univ_inter] at hfu hgv
    let s := u ∩ v
    have hs : UniqueDiffOn ℝ s := (hu.inter hv).uniqueDiffOn
    have hxs : x ∈ s := ⟨hxu, hxv⟩
    have hzero : iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m • (g y - g x)) x = 0 := by
      have hbound := norm_iteratedFDerivWithin_smul_le
        (hfu.mono Set.inter_subset_left) (hgv.mono Set.inter_subset_right) hs hxs
        (show (k : ℕ∞ω) ≤ k from le_rfl)
      rw [iteratedFDerivWithin_eq_iteratedFDeriv (n := k)
        (f := fun y ↦ (f y) ^ m • (g y - g x)) hs
        ((hpower.smul hdiff).of_le (by simp)) hxs] at hbound
      have hsum : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun y ↦ (f y) ^ m) s x‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun y ↦ g y - g x) s x‖) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        by_cases him : i < m
        · rw [iteratedFDerivWithin_eq_iteratedFDeriv (n := i) hs
            (hpower.of_le (by simp)) hxs,
            power_jet_zero f x hf hx m i him]
          simp
        · have hki : k - i = 0 := by omega
          rw [hki, norm_iteratedFDerivWithin_zero, sub_self, norm_zero, mul_zero]
      rw [hsum] at hbound
      exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
    have hsub : (fun y ↦ (f y) ^ m • (g y - g x)) =
        (fun y ↦ (f y) ^ m • g y) - (fun y ↦ (f y) ^ m • g x) := by
      funext y
      exact smul_sub _ _ _
    rw [hsub, iteratedFDeriv_sub_apply (i := k)
      (f := fun y ↦ (f y) ^ m • g y) (g := fun y ↦ (f y) ^ m • g x)
      ((hpower.smul hg).of_le (by simp))
      ((hpower.smul (contDiffAt_const (c := g x))).of_le (by simp))] at hzero
    exact sub_eq_zero.mp hzero
  -- Stage 3: the original finite expression detects exactly its highest-order symbol.
  have coordinate_apply_power {n r q m : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
      (Q : AtiyahSinger.CoordinateDifferentialOperator n r q m U)
      (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
      (x : EuclideanSpace ℝ (Fin n)) (hf : ContDiffAt ℝ ∞ f x)
      (hg : ContDiffAt ℝ ∞ g x) (hx : f x = 0) :
      Q.apply (fun y ↦ (f y) ^ m • g y) x =
        ((-Complex.I) ^ m * (m.factorial : ℂ)) •
          Q.principalSymbol x
            (WithLp.toLp 2 fun j ↦ fderiv ℝ f x (EuclideanSpace.single j 1)) (g x) := by
    classical
    have hjet (k : ℕ) (hk : k ≤ m) := power_smul_jet f g x hf hg hx m k hk
    have hzero (k : ℕ) (hk : k < m) :
        iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m • g y) x = 0 := by
      rw [hjet k (Nat.le_of_lt hk),
        iteratedFDeriv_smul_const_apply ((hf.pow m).of_le (by simp)),
        power_jet_zero f x hf hx m k hk]
      ext v
      simp
    have htop (α : Fin m → Fin n) :
        iteratedFDeriv ℝ m (fun y ↦ (f y) ^ m • g y) x
          (fun j ↦ EuclideanSpace.single (α j) 1) =
        (m.factorial : ℝ) • (∏ j, fderiv ℝ f x (EuclideanSpace.single (α j) 1)) • g x := by
      rw [hjet m le_rfl, iteratedFDeriv_smul_const_apply ((hf.pow m).of_le (by simp))]
      change (iteratedFDeriv ℝ m (fun y ↦ (f y) ^ m) x
        (fun j ↦ EuclideanSpace.single (α j) 1)) • g x = _
      rw [power_jet_top f x hf hx m, mul_smul]
    unfold AtiyahSinger.CoordinateDifferentialOperator.apply
    rw [Finset.sum_eq_single (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))]
    · simp only [htop]
      simp only [AtiyahSinger.CoordinateDifferentialOperator.principalSymbol,
        _root_.sum_apply, smul_apply, ← Complex.coe_smul, Complex.ofReal_natCast,
        map_smul, mul_smul, Finset.smul_sum]
    · intro k _ hk
      have hkm : k.val < m := lt_of_le_of_ne (Nat.le_of_lt_succ k.isLt)
        (fun h ↦ hk (Fin.ext h))
      apply Finset.sum_eq_zero
      intro α _
      simp [hzero k.val hkm]
    · simp
  -- Pass from one actual coordinate expression to the original global symbol.
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
  have hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M := chart_mem_atlas _ x
  obtain ⟨U, hU, hxU, Q, hQ⟩ := P.isDifferentialOperator c hc e f x
    ⟨⟨mem_chart_source _ x, he⟩, hf⟩
  let ξ := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x
  have hφd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x = ξ := rfl
  have htest : f.linearMapAt ℂ x ((P.toLinearMap t).val x) =
      ((-Complex.I) ^ d * (d.factorial : ℂ)) •
        Q.principalSymbol (c x) (covectorInChart c x ξ)
          (e.linearMapAt ℂ x (s.val x)) := by
    have hx := hQ.1 hxU
    let ψ : EuclideanSpace ℝ (Fin n) → ℝ := φ ∘ c.symm
    let g := sectionInChart E c e s.val
    have hcsm := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) hc) (c.map_source hx.1.1)
    have hψ : ContDiffAt ℝ ∞ ψ (c x) :=
      (hφ.contMDiffAt.comp (c x) hcsm).contDiffAt
    have hg : ContDiffAt ℝ ∞ g (c x) := by
      have hsection := (s.property e inferInstance).contMDiffAt
        (e.open_baseSet.mem_nhds (show c.symm (c x) ∈ e.baseSet by
          simpa [c.left_inv hx.1.1] using hx.1.2))
      exact (hsection.comp (c x) hcsm).contDiffAt
    have hψx : ψ (c x) = 0 := by simp [ψ, c.left_inv hx.1.1, hφx]
    have hcoords : sectionInChart E c e t.val =ᶠ[𝓝 (c x)]
        (fun z ↦ (ψ z) ^ d • g z) := by
      filter_upwards [(c.tendsto_symm hx.1.1).eventually
        (e.open_baseSet.mem_nhds hx.1.2)] with z hz
      dsimp only [sectionInChart, ψ, g, Function.comp_apply]
      rw [ht]
      change (e.linearEquivAt ℂ (c.symm z) hz) (((φ (c.symm z)) ^ d : ℂ) •
        s.val (c.symm z)) = _
      rw [map_smul, ← Complex.ofReal_pow, Complex.coe_smul]
      rfl
    have happly : Q.apply (sectionInChart E c e t.val) (c x) =
        Q.apply (fun z ↦ (ψ z) ^ d • g z) (c x) := by
      simp only [CoordinateDifferentialOperator.apply]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro α _
      rw [(hcoords.iteratedFDeriv ℝ k.val).eq_of_nhds]
    have hdψ : fderiv ℝ ψ (c x) =
        ξ.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm (c x)) := by
      have hchain := mfderiv_comp (c x) (hφ.contMDiffAt.mdifferentiableAt (by simp))
        (hcsm.mdifferentiableAt (by simp))
      dsimp only [ψ]
      have hleft : c.symm (c x) = x := c.left_inv hx.1.1
      erw [hleft, hφd] at hchain
      rw [mfderiv_eq_fderiv] at hchain
      exact hchain
    have hcov : (WithLp.toLp 2 fun j ↦ fderiv ℝ ψ (c x)
        (EuclideanSpace.single j 1)) = covectorInChart c x ξ := by
      rw [hdψ]
      rfl
    simp only [f.coe_linearMapAt_of_mem hx.2]
    rw [hQ.2 t x hxU, happly,
      coordinate_apply_power Q ψ g (c x) hψ hg hψx, hcov]
    congr 1
    dsimp only [g, sectionInChart]
    rw [c.left_inv hx.1.1, e.coe_linearMapAt_of_mem hx.1.2]
  have hsymbol := LinearMap.congr_fun
    (P.hasPrincipalSymbol c hc e f U hU Q hQ x hxU ξ) (s.val x)
  apply (f.linearEquivAt ℂ x hf).injective
  have heq := htest.trans
    (congrArg (((-Complex.I) ^ d * (d.factorial : ℂ)) • ·) hsymbol.symm)
  simpa only [f.linearMapAt_def_of_mem hf, map_smul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ξ] using heq

end DifferentialOperator

include hM hT2 hSC hBorel hE hF hμ

set_option maxHeartbeats 1000000 in
-- Evaluate the repeated compact-test commutators on the original two symbol fibers.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- Compact-test adjunction determines the metric adjoint of every principal-symbol fiber map. -/
theorem IsCompactTestMetricFormalAdjoint.principalSymbol_pairing {d : ℕ}
    {P : DifferentialOperator (n := n) (r := r) (q := q) E F d}
    {Q : DifferentialOperator (n := n) (r := q) (q := r) F E d}
    (hPQ : IsCompactTestMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
    (u : E x) (v : F x) :
    k.pairing x (P.principalSymbol x ξ u) v =
      h.pairing x u (Q.principalSymbol x ξ v) := by
  classical
  -- Repeated commutators are shifted scalar powers after evaluation at one point.
  have comm_evalP {A B W : Type _} [AddCommGroup A] [Module ℂ A]
      [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W]
      (a : A →ₗ[ℂ] A) (b : B →ₗ[ℂ] B) (L : A →ₗ[ℂ] B)
      (e : B →ₗ[ℂ] W) (z : ℂ) (he : ∀ v, e (b v) = z • e v) :
      ∀ (j : ℕ) (u : A),
        e ((Nat.rec (motive := fun _ ↦ A →ₗ[ℂ] B) L
          (fun _ T ↦ T.comp a - b.comp T) j) u) =
        e (L (((a - z • (LinearMap.id : A →ₗ[ℂ] A)) ^ j) u)) := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih =>
      intro u
      change e ((Nat.rec (motive := fun _ ↦ A →ₗ[ℂ] B) L (fun _ T ↦ T.comp a - b.comp T) j) (a u) -
        b ((Nat.rec (motive := fun _ ↦ A →ₗ[ℂ] B) L (fun _ T ↦ T.comp a - b.comp T) j) u)) = _
      rw [map_sub, he, ih, ih, ← map_smul, ← map_sub, ← map_smul, ← map_sub]
      congr 2
      rw [← map_smul, ← map_sub]
      change ((a - z • (LinearMap.id : A →ₗ[ℂ] A)) ^ j) ((a - z • (LinearMap.id : A →ₗ[ℂ] A)) u) = _
      rw [pow_succ]
      rfl
  have comm_evalQ {A B W : Type _} [AddCommGroup A] [Module ℂ A]
      [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W]
      (a : A →ₗ[ℂ] A) (b : B →ₗ[ℂ] B) (L : A →ₗ[ℂ] B)
      (e : B →ₗ[ℂ] W) (z : ℂ) (he : ∀ v, e (b v) = z • e v) :
      ∀ (j : ℕ) (u : A),
        e ((Nat.rec (motive := fun _ ↦ A →ₗ[ℂ] B) L
          (fun _ T ↦ T.comp a - b.comp T) j) u) =
        e (L (((a - z • (LinearMap.id : A →ₗ[ℂ] A)) ^ j) u)) := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih =>
      intro u
      change e ((Nat.rec (motive := fun _ ↦ A →ₗ[ℂ] B) L (fun _ T ↦ T.comp a - b.comp T) j) (a u) -
        b ((Nat.rec (motive := fun _ ↦ A →ₗ[ℂ] B) L (fun _ T ↦ T.comp a - b.comp T) j) u)) = _
      rw [map_sub, he, ih, ih, ← map_smul, ← map_sub, ← map_smul, ← map_sub]
      congr 2
      rw [← map_smul, ← map_sub]
      change ((a - z • (LinearMap.id : A →ₗ[ℂ] A)) ^ j) ((a - z • (LinearMap.id : A →ₗ[ℂ] A)) u) = _
      rw [pow_succ]
      rfl
  have pow_evalP {A B : Type _} [AddCommGroup A] [Module ℂ A]
      [AddCommGroup B] [Module ℂ B] (a : A →ₗ[ℂ] A) (e : A →ₗ[ℂ] B)
      (z : ℂ) (he : ∀ u, e (a u) = z • e u) :
      ∀ (j : ℕ) (u : A), e ((a ^ j) u) = z ^ j • e u := by
    intro j
    induction j with
    | zero => intro u; simp
    | succ j ih =>
      intro u
      rw [pow_succ', Module.End.mul_apply, he, ih, pow_succ', mul_smul]
  have pow_evalQ {A B : Type _} [AddCommGroup A] [Module ℂ A]
      [AddCommGroup B] [Module ℂ B] (a : A →ₗ[ℂ] A) (e : A →ₗ[ℂ] B)
      (z : ℂ) (he : ∀ u, e (a u) = z • e u) :
      ∀ (j : ℕ) (u : A), e ((a ^ j) u) = z ^ j • e u := by
    intro j
    induction j with
    | zero => intro u; simp
    | succ j ih =>
      intro u
      rw [pow_succ', Module.End.mul_apply, he, ih, pow_succ', mul_smul]
  have reverse_comm {A B : Type _} [AddCommGroup A] [Module ℂ A]
      [AddCommGroup B] [Module ℂ B]
      (a : A →ₗ[ℂ] A) (b : B →ₗ[ℂ] B) (L : A →ₗ[ℂ] B) :
      ∀ j : ℕ, Nat.rec (motive := fun _ ↦ A →ₗ[ℂ] B) L (fun _ T ↦ b.comp T - T.comp a) j =
        (-1 : ℂ) ^ j • Nat.rec (motive := fun _ ↦ A →ₗ[ℂ] B) L
          (fun _ T ↦ T.comp a - b.comp T) j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      simp only
      rw [ih]
      ext u
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        map_smul, pow_succ, mul_smul, neg_one_smul]
      change (-1 : ℂ) ^ j • b _ - (-1 : ℂ) ^ j • _ =
        (-1 : ℂ) ^ j • -(_ - b _)
      rw [neg_sub, smul_sub]
      rfl
  have exists_sectionE (x : M) (v : E x) :
      ∃ (K : Set M), IsCompact K ∧
        ∃ s : supportedSmoothSections (n := n) (r := r) E K, s.val.val x = v := by
    classical
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (e.open_baseSet.mem_nhds hx)
    let a : EuclideanSpace ℂ (Fin r) := (e.linearEquivAt ℂ x hx) v
    let s : ∀ y, E y := fun y ↦ (b y : ℂ) • e.symmL ℂ y a
    have hs : AtiyahSinger.IsSmoothSection (n := n) (r := r) E s := by
      intro f hf y hy
      let := hf
      by_cases hyb : y ∈ tsupport b
      · have hye : y ∈ e.baseSet := hb hyb
        have htransition :=
          (AtiyahSinger.IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e f).contMDiffAt
            ((e.open_baseSet.inter f.open_baseSet).mem_nhds ⟨hye, hy⟩)
        have happly : ContDiff ℝ ∞
            (fun L : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r) ↦ L a) :=
          (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
        have hcoord := happly.comp_contMDiffAt htransition
        have hscalar := Complex.ofRealCLM.contMDiff.comp b.contMDiff
        have hmul : ContDiff ℝ ∞
            (fun p : ℂ × EuclideanSpace ℂ (Fin r) ↦ p.1 • p.2) := contDiff_smul
        have hlocal := hmul.comp_contMDiffAt (hscalar.contMDiffAt.prodMk_space hcoord)
        apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [e.open_baseSet.mem_nhds hye, f.open_baseSet.mem_nhds hy]
          with z hze hzf
        change (f.linearEquivAt ℂ z hzf) ((b z : ℂ) • e.symmL ℂ z a) =
          (b z : ℂ) • e.coordChangeL ℂ f z a
        rw [map_smul, e.coordChangeL_apply f ⟨hze, hzf⟩, e.symmL_apply hze]
        rfl
      · apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r)))
          |>.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [((isClosed_tsupport b).isOpen_compl.mem_nhds hyb),
          f.open_baseSet.mem_nhds hy] with z hzb hzf
        change (f.linearEquivAt ℂ z hzf) ((b z : ℂ) • e.symmL ℂ z a) = 0
        rw [image_eq_zero_of_notMem_tsupport hzb, Complex.ofReal_zero, zero_smul, map_zero]
    refine ⟨tsupport b, b.hasCompactSupport, ⟨⟨s, hs⟩, ?_⟩, ?_⟩
    · intro y hy
      change (b y : ℂ) • e.symmL ℂ y a = 0
      rw [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_smul]
    · dsimp only [s]
      rw [b.eq_one, Complex.ofReal_one, one_smul, e.symmL_apply hx]
      exact e.symm_apply_apply_mk hx v
  have exists_sectionF (x : M) (v : F x) :
      ∃ (K : Set M), IsCompact K ∧
        ∃ s : supportedSmoothSections (n := n) (r := q) F K, s.val.val x = v := by
    classical
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let e := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (e.open_baseSet.mem_nhds hx)
    let a : EuclideanSpace ℂ (Fin q) := (e.linearEquivAt ℂ x hx) v
    let s : ∀ y, F y := fun y ↦ (b y : ℂ) • e.symmL ℂ y a
    have hs : AtiyahSinger.IsSmoothSection (n := n) (r := q) F s := by
      intro f hf y hy
      let := hf
      by_cases hyb : y ∈ tsupport b
      · have hye : y ∈ e.baseSet := hb hyb
        have htransition :=
          (AtiyahSinger.IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e f).contMDiffAt
            ((e.open_baseSet.inter f.open_baseSet).mem_nhds ⟨hye, hy⟩)
        have happly : ContDiff ℝ ∞
            (fun L : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q) ↦ L a) :=
          (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
        have hcoord := happly.comp_contMDiffAt htransition
        have hscalar := Complex.ofRealCLM.contMDiff.comp b.contMDiff
        have hmul : ContDiff ℝ ∞
            (fun p : ℂ × EuclideanSpace ℂ (Fin q) ↦ p.1 • p.2) := contDiff_smul
        have hlocal := hmul.comp_contMDiffAt (hscalar.contMDiffAt.prodMk_space hcoord)
        apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [e.open_baseSet.mem_nhds hye, f.open_baseSet.mem_nhds hy]
          with z hze hzf
        change (f.linearEquivAt ℂ z hzf) ((b z : ℂ) • e.symmL ℂ z a) =
          (b z : ℂ) • e.coordChangeL ℂ f z a
        rw [map_smul, e.coordChangeL_apply f ⟨hze, hzf⟩, e.symmL_apply hze]
        rfl
      · apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin q)))
          |>.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [((isClosed_tsupport b).isOpen_compl.mem_nhds hyb),
          f.open_baseSet.mem_nhds hy] with z hzb hzf
        change (f.linearEquivAt ℂ z hzf) ((b z : ℂ) • e.symmL ℂ z a) = 0
        rw [image_eq_zero_of_notMem_tsupport hzb, Complex.ofReal_zero, zero_smul, map_zero]
    refine ⟨tsupport b, b.hasCompactSupport, ⟨⟨s, hs⟩, ?_⟩, ?_⟩
    · intro y hy
      change (b y : ℂ) • e.symmL ℂ y a = 0
      rw [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_smul]
    · dsimp only [s]
      rw [b.eq_one, Complex.ofReal_one, one_smul, e.symmL_apply hx]
      exact e.symm_apply_apply_mk hx v
  have exists_scalar_jet (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      ∃ φ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ ∧
        φ x = 0 ∧ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x = ξ := by
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let b : SmoothBumpFunction I x := Classical.choice inferInstance
    let ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
      ξ.comp (mfderiv I I c.symm (c x))
    let φ : M → ℝ := fun y ↦ b y * ℓ (c y - c x)
    have hc := contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) (chart_mem_atlas _ x))
    have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ :=
      b.contMDiff_smul (ℓ.contMDiff.comp_contMDiffOn (hc.sub contMDiffOn_const))
    have heq : φ =ᶠ[𝓝 x] (fun y ↦ ℓ (c y - c x)) := by
      filter_upwards [b.eventuallyEq_one] with y hy
      simp [φ, hy]
    refine ⟨φ, hs, ?_, ?_⟩
    · simp [φ]
    · rw [heq.mfderiv_eq]
      have hchart := mdifferentiable_of_mem_atlas (I := I) (chart_mem_atlas _ x)
      have hcx := hchart.mdifferentiableAt (mem_chart_source _ x)
      change mfderiv I 𝓘(ℝ, ℝ) (ℓ ∘ (fun y ↦ c y - c x)) x = ξ
      erw [mfderiv_comp x (ℓ.contMDiff (n := ∞) |>.contMDiffAt.mdifferentiableAt (by simp))
        (hcx.sub (mdifferentiableAt_const (c := c x))), mfderiv_eq_fderiv, ℓ.fderiv,
        mfderiv_sub hcx (mdifferentiableAt_const (c := c x)), mfderiv_const, sub_zero]
      dsimp only [ℓ]
      change (ξ.comp (mfderiv I I c.symm (c x))).comp (mfderiv I I c x) = ξ
      erw [ContinuousLinearMap.comp_assoc, hchart.symm_comp_deriv (mem_chart_source _ x)]
      exact ContinuousLinearMap.comp_id ξ
  obtain ⟨φ, hφ, hφx, hφd⟩ := exists_scalar_jet x ξ
  let SE := smoothSections (n := n) (r := r) E
  let SF := smoothSections (n := n) (r := q) F
  let a : SE →ₗ[ℂ] SE := smoothSectionMul E (fun y ↦ (φ y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hφ)
  let b : SF →ₗ[ℂ] SF := smoothSectionMul F (fun y ↦ (φ y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hφ)
  let CP : ℕ → SE →ₗ[ℂ] SF :=
    Nat.rec P.toLinearMap (fun _ T ↦ T.comp a - b.comp T)
  let CQ : ℕ → SF →ₗ[ℂ] SE :=
    Nat.rec Q.toLinearMap (fun _ T ↦ T.comp b - a.comp T)
  let RQ : ℕ → SF →ₗ[ℂ] SE :=
    Nat.rec Q.toLinearMap (fun _ T ↦ a.comp T - T.comp b)
  let evE (y : M) : SE →ₗ[ℂ] E y :=
    (LinearMap.proj y).comp (smoothSections (n := n) (r := r) E).subtype
  let evF (y : M) : SF →ₗ[ℂ] F y :=
    (LinearMap.proj y).comp (smoothSections (n := n) (r := q) F).subtype
  let C : ℂ := (-Complex.I) ^ d * (d.factorial : ℂ)
  have evalP (s : SE) (y : M) :
      (CP d s).val y = C • P.principalSymbol y
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ y) (s.val y) := by
    let t : SE := ((a - (φ y : ℂ) • (LinearMap.id : SE →ₗ[ℂ] SE)) ^ d) s
    have ht (z : M) : t.val z = ((φ z - φ y : ℝ) : ℂ) ^ d • s.val z := by
      have hh := pow_evalP (a - (φ y : ℂ) • (LinearMap.id : SE →ₗ[ℂ] SE))
        (evE z) ((φ z : ℂ) - (φ y : ℂ)) (fun (w : SE) ↦ by
          change (φ z : ℂ) • w.val z - (φ y : ℂ) • w.val z = _
          exact (sub_smul _ _ _).symm) d s
      change t.val z = ((φ z : ℂ) - (φ y : ℂ)) ^ d • s.val z at hh
      simpa only [Complex.ofReal_sub] using hh
    have hc := comm_evalP a b P.toLinearMap (evF y) (φ y : ℂ) (fun _ ↦ rfl) d s
    change (CP d s).val y = (P.toLinearMap t).val y at hc
    rw [hc, P.apply_scalar_pow (fun z ↦ φ z - φ y) (hφ.sub contMDiff_const) y
      (sub_self _) s t ht]
    congr 2
    erw [mfderiv_sub (hφ.contMDiffAt.mdifferentiableAt (by simp))
      (mdifferentiableAt_const (c := φ y)), mfderiv_const, sub_zero]
  have evalQ (s : SF) (y : M) :
      (CQ d s).val y = C • Q.principalSymbol y
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ y) (s.val y) := by
    let t : SF := ((b - (φ y : ℂ) • (LinearMap.id : SF →ₗ[ℂ] SF)) ^ d) s
    have ht (z : M) : t.val z = ((φ z - φ y : ℝ) : ℂ) ^ d • s.val z := by
      have hh := pow_evalQ (b - (φ y : ℂ) • (LinearMap.id : SF →ₗ[ℂ] SF))
        (evF z) ((φ z : ℂ) - (φ y : ℂ)) (fun (w : SF) ↦ by
          change (φ z : ℂ) • w.val z - (φ y : ℂ) • w.val z = _
          exact (sub_smul _ _ _).symm) d s
      change t.val z = ((φ z : ℂ) - (φ y : ℂ)) ^ d • s.val z at hh
      simpa only [Complex.ofReal_sub] using hh
    have hc := comm_evalQ b a Q.toLinearMap (evE y) (φ y : ℂ) (fun _ ↦ rfl) d s
    change (CQ d s).val y = (Q.toLinearMap t).val y at hc
    rw [hc, Q.apply_scalar_pow (fun z ↦ φ z - φ y) (hφ.sub contMDiff_const) y
      (sub_self _) s t ht]
    congr 2
    erw [mfderiv_sub (hφ.contMDiffAt.mdifferentiableAt (by simp))
      (mdifferentiableAt_const (c := φ y)), mfderiv_const, sub_zero]
  have evalR (s : SF) (y : M) :
      (RQ d s).val y = conj C • Q.principalSymbol y
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ y) (s.val y) := by
    have hR : RQ d = (-1 : ℂ) ^ d • CQ d := reverse_comm b a Q.toLinearMap d
    rw [hR]
    change (-1 : ℂ) ^ d • (CQ d s).val y = _
    rw [evalQ, smul_smul]
    congr 1
    simp only [C, map_mul, map_pow, map_neg, Complex.conj_I, neg_neg, map_natCast]
    rw [← mul_assoc, ← mul_pow]
    congr 2
    ring
  -- Compact support provides every integral used in the commutator adjunction.
  have integralF (L : Set M) (hL : IsCompact L)
      (t : supportedSmoothSections (n := n) (r := q) F L) (s : SF) :
      Integrable (fun y ↦ k.pairing y (s.val y) (t.val.val y)) μ := by
    have hh := Complex.conjCLE.toContinuousLinearMap.integrable_comp
      (k.integrable_pairing_of_supported μ L hL t s)
    apply hh.congr
    filter_upwards [] with y
    exact (k.toCore y).conj_inner_symm _ _
  have subF (L : Set M) (hL : IsCompact L)
      (t : supportedSmoothSections (n := n) (r := q) F L) (s₁ s₂ : SF) :
      k.sectionPairing μ (s₁ - s₂) t.val =
        k.sectionPairing μ s₁ t.val - k.sectionPairing μ s₂ t.val := by
    have hh (y : M) : k.pairing y (s₁.val y - s₂.val y) (t.val.val y) =
        k.pairing y (s₁.val y) (t.val.val y) -
          k.pairing y (s₂.val y) (t.val.val y) := by
      let : InnerProductSpace.Core ℂ (F y) := k.toCore y
      exact InnerProductSpace.Core.inner_sub_left _ _ _
    change (∫ y, k.pairing y (s₁.val y - s₂.val y) (t.val.val y) ∂μ) = _
    simp_rw [hh]
    exact integral_sub (integralF L hL t s₁) (integralF L hL t s₂)
  have subE (K : Set M) (hK : IsCompact K)
      (s : supportedSmoothSections (n := n) (r := r) E K) (t₁ t₂ : SE) :
      h.sectionPairing μ s.val (t₁ - t₂) =
        h.sectionPairing μ s.val t₁ - h.sectionPairing μ s.val t₂ := by
    have hh (y : M) : h.pairing y (s.val.val y) (t₁.val y - t₂.val y) =
        h.pairing y (s.val.val y) (t₁.val y) -
          h.pairing y (s.val.val y) (t₂.val y) := by
      let : InnerProductSpace.Core ℂ (E y) := h.toCore y
      exact InnerProductSpace.Core.inner_sub_right _ _ _
    change (∫ y, h.pairing y (s.val.val y) (t₁.val y - t₂.val y) ∂μ) = _
    simp_rw [hh]
    exact integral_sub (h.integrable_pairing_of_supported μ K hK s t₁)
      (h.integrable_pairing_of_supported μ K hK s t₂)
  have smulLeftE (y : M) (z : ℂ) (w t : E y) :
      h.pairing y (z • w) t = conj z * h.pairing y w t := (h.toCore y).smul_left _ _ _
  have smulLeftF (y : M) (z : ℂ) (w t : F y) :
      k.pairing y (z • w) t = conj z * k.pairing y w t := (k.toCore y).smul_left _ _ _
  have smulE (y : M) (z : ℂ) (w t : E y) :
      h.pairing y w (z • t) = z * h.pairing y w t := by
    let : InnerProductSpace.Core ℂ (E y) := h.toCore y
    exact InnerProductSpace.Core.inner_smul_right _ _
  have smulF (y : M) (z : ℂ) (w t : F y) :
      k.pairing y w (z • t) = z * k.pairing y w t := by
    let : InnerProductSpace.Core ℂ (F y) := k.toCore y
    exact InnerProductSpace.Core.inner_smul_right _ _
  have moveE (s t : SE) : h.sectionPairing μ (a s) t = h.sectionPairing μ s (a t) := by
    apply integral_congr_ae
    filter_upwards [] with y
    change h.pairing y ((φ y : ℂ) • s.val y) (t.val y) =
      h.pairing y (s.val y) ((φ y : ℂ) • t.val y)
    let : InnerProductSpace.Core ℂ (E y) := h.toCore y
    rw [smulLeftE, smulE]
    simp
  have moveF (s t : SF) : k.sectionPairing μ (b s) t = k.sectionPairing μ s (b t) := by
    apply integral_congr_ae
    filter_upwards [] with y
    change k.pairing y ((φ y : ℂ) • s.val y) (t.val y) =
      k.pairing y (s.val y) ((φ y : ℂ) • t.val y)
    let : InnerProductSpace.Core ℂ (F y) := k.toCore y
    rw [smulLeftF, smulF]
    simp
  have adjunction (j : ℕ) : IsCompactTestMetricFormalAdjoint h k μ (CP j) (RQ j) := by
    induction j with
    | zero => exact hPQ
    | succ j ih =>
      intro K L hK hL s t
      let sφ : supportedSmoothSections (n := n) (r := r) E K :=
        ⟨a s.val, fun y hy ↦ by
          change (φ y : ℂ) • s.val.val y = 0
          rw [s.property y hy, smul_zero]⟩
      let tφ : supportedSmoothSections (n := n) (r := q) F L :=
        ⟨b t.val, fun y hy ↦ by
          change (φ y : ℂ) • t.val.val y = 0
          rw [t.property y hy, smul_zero]⟩
      change k.sectionPairing μ (CP j (a s.val) - b (CP j s.val)) t.val =
        h.sectionPairing μ s.val (a (RQ j t.val) - RQ j (b t.val))
      rw [subF L hL t, subE K hK s, moveF, ← moveE]
      exact congrArg₂ (· - ·) (ih K L hK hL sφ t) (ih K L hK hL s tφ)
  -- At top order the commutator is a fiber map and commutes with every smooth scalar.
  have mulCP (g : M → ℂ)
      (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ g)
      (s : SE) (y : M) :
      (CP d (smoothSectionMul E g hg s)).val y = g y • (CP d s).val y := by
    rw [evalP, evalP, smoothSectionMul_apply, map_smul, smul_comm]
  by_cases hu : u = 0
  · subst u
    rw [map_zero]
    have hzE : h.pairing x 0 (Q.principalSymbol x ξ v) = 0 := by
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      exact InnerProductSpace.Core.inner_zero_left _
    have hzF : k.pairing x 0 v = 0 := by
      let : InnerProductSpace.Core ℂ (F x) := k.toCore x
      exact InnerProductSpace.Core.inner_zero_left _
    rw [hzE, hzF]
  obtain ⟨K, hK, s, hs⟩ := exists_sectionE x u
  obtain ⟨L, hL, t, ht⟩ := exists_sectionF x v
  let f (y : M) : ℂ := k.pairing y ((CP d s.val).val y) (t.val.val y) -
    h.pairing y (s.val.val y) ((RQ d t.val).val y)
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ f :=
    (k.contMDiff_pairing _ _).sub (h.contMDiff_pairing _ _)
  let g (y : M) : ℂ := f y * h.pairing y (s.val.val y) (s.val.val y)
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ g :=
    (contDiff_mul : ContDiff ℝ ∞ (fun p : ℂ × ℂ ↦ p.1 * p.2)).comp_contMDiff
      (hf.prodMk_space (h.contMDiff_pairing _ _))
  let s' : supportedSmoothSections (n := n) (r := r) E K :=
    ⟨smoothSectionMul E g hg s.val, fun y hy ↦ by
      change g y • s.val.val y = 0
      rw [s.property y hy, smul_zero]⟩
  let w : supportedSmoothSections (n := n) (r := r) E K :=
    ⟨smoothSectionMul E f hf s.val, fun y hy ↦ by
      change f y • s.val.val y = 0
      rw [s.property y hy, smul_zero]⟩
  -- Testing with the scalar discrepancy times the source norm gives a nonnegative square.
  have hself : h.sectionPairing μ w.val w.val = 0 := by
    have hpoint (y : M) : h.pairing y (w.val.val y) (w.val.val y) =
        k.pairing y ((CP d s'.val).val y) (t.val.val y) -
          h.pairing y (s'.val.val y) ((RQ d t.val).val y) := by
      change h.pairing y (f y • s.val.val y) (f y • s.val.val y) =
        k.pairing y ((CP d (smoothSectionMul E g hg s.val)).val y) (t.val.val y) -
          h.pairing y (g y • s.val.val y) ((RQ d t.val).val y)
      rw [mulCP, smulLeftE, smulE, smulLeftF, smulLeftE]
      have hreal : conj (h.pairing y (s.val.val y) (s.val.val y)) =
          h.pairing y (s.val.val y) (s.val.val y) := (h.toCore y).conj_inner_symm _ _
      dsimp only [g]
      rw [map_mul, hreal]
      dsimp only [f]
      ring
    calc
      h.sectionPairing μ w.val w.val =
          ∫ y, k.pairing y ((CP d s'.val).val y) (t.val.val y) -
            h.pairing y (s'.val.val y) ((RQ d t.val).val y) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = k.sectionPairing μ (CP d s'.val) t.val -
          h.sectionPairing μ s'.val (RQ d t.val) :=
        integral_sub (integralF L hL t _) (h.integrable_pairing_of_supported μ K hK s' _)
      _ = 0 := sub_eq_zero.mpr (adjunction d K L hK hL s' t)
  have hw := (h.sectionPairing_self_eq_zero_iff_of_supported μ K hK w).mp hself
  have hwx : f x • s.val.val x = 0 := congrArg (fun z ↦ z.val.val x) hw
  have hfzero : f x = 0 := (smul_eq_zero.mp hwx).resolve_right (hs ▸ hu)
  have hpair : k.pairing x ((CP d s.val).val x) (t.val.val x) =
      h.pairing x (s.val.val x) ((RQ d t.val).val x) := sub_eq_zero.mp hfzero
  rw [evalP, evalR, hφd, hs, ht, smulLeftF, smulE] at hpair
  have hC : conj C ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr (mul_ne_zero
    (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
    (by exact_mod_cast Nat.factorial_ne_zero d))
  exact mul_left_cancel₀ hC hpair


namespace DifferentialOperator

variable {d : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F d)

set_option maxHeartbeats 2000000 in
-- Assemble local adjoints from the same Gram matrices and prove compact-test uniqueness.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- Compactly supported metric tests determine a unique differential adjoint of the same order
bound, without compactness of the base manifold. -/
theorem existsUnique_compactTestMetricFormalAdjoint :
    ∃! Q : DifferentialOperator (n := n) (r := q) (q := r) F E d,
      IsCompactTestMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap := by
  classical
  let TModel := EuclideanSpace ℝ (Fin n)
  let SourceModel := EuclideanSpace ℂ (Fin r)
  let TargetModel := EuclideanSpace ℂ (Fin q)
  -- Smooth positive Gram matrices are invertible in the original two frame overlaps.
  have hgramE (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (e : Trivialization SourceModel (π SourceModel E)) [MemTrivializationAtlas e] :
      ∃ G : TModel → (SourceModel →L[ℂ] SourceModel),
        ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ∀ z ∈ c.target ∩ c.symm ⁻¹' e.baseSet,
          (∃ L : SourceModel ≃L[ℂ] SourceModel, L.toContinuousLinearMap = G z) ∧
          (∀ u v : SourceModel,
            h.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
              inner ℂ u (G z v)) := by
    classical
    let toOp : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (SourceModel →L[ℂ] SourceModel) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (z : TModel) : SourceModel →L[ℂ] SourceModel := toOp (h.gramMatrix e (c.symm z))
    have hG (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) : ContDiffAt ℝ ∞ G z := by
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, TModel)) (n := ∞) hc) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact (((h.contMDiffOn_gram e i j).contMDiffAt
        (e.open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    have hpair (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) (u v : SourceModel) :
        h.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
          inner ℂ u (G z v) := by
      have hcoords (a : SourceModel) : (e ⟨c.symm z, e.symmL ℂ (c.symm z) a⟩).2 = a := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 a
      rw [h.pairing_eq_gramMatrix e _ hz.2, hcoords u, hcoords v, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j, conj (u i) * h.gramMatrix e (c.symm z) i j * v j) =
        (∑ j, h.gramMatrix e (c.symm z) i j * v j) * conj (u i)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hequiv (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) :
        ∃ L : SourceModel ≃L[ℂ] SourceModel, L.toContinuousLinearMap = G z := by
      have hinj : Function.Injective (G z) := by
        intro u v huv
        have hzG : G z (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have hzpair := hpair z hz (u - v) (u - v)
        rw [hzG, inner_zero_right] at hzpair
        have hzvec : e.symmL ℂ (c.symm z) (u - v) = 0 :=
          (h.toCore _).definite _ hzpair
        have hzcoords := congrArg (e.continuousLinearMapAt ℂ (c.symm z)) hzvec
        rw [e.continuousLinearMapAt_symmL hz.2, map_zero] at hzcoords
        exact sub_eq_zero.mp hzcoords
      exact ⟨(LinearEquiv.ofBijective (G z).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
    refine ⟨G, fun z hz ↦ (hG z hz).contDiffWithinAt, ?_, ?_⟩
    · intro z hz
      obtain ⟨L, hL⟩ := hequiv z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact (hi.comp z (hG z hz)).contDiffWithinAt
    · intro z hz
      exact ⟨hequiv z hz, hpair z hz⟩
  have hgramF (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (e : Trivialization TargetModel (π TargetModel F)) [MemTrivializationAtlas e] :
      ∃ G : TModel → (TargetModel →L[ℂ] TargetModel),
        ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ∀ z ∈ c.target ∩ c.symm ⁻¹' e.baseSet,
          (∃ L : TargetModel ≃L[ℂ] TargetModel, L.toContinuousLinearMap = G z) ∧
          (∀ u v : TargetModel,
            k.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
              inner ℂ u (G z v)) := by
    classical
    let toOp : Matrix (Fin q) (Fin q) ℂ →L[ℝ] (TargetModel →L[ℂ] TargetModel) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (z : TModel) : TargetModel →L[ℂ] TargetModel := toOp (k.gramMatrix e (c.symm z))
    have hG (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) : ContDiffAt ℝ ∞ G z := by
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, TModel)) (n := ∞) hc) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact (((k.contMDiffOn_gram e i j).contMDiffAt
        (e.open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    have hpair (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) (u v : TargetModel) :
        k.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
          inner ℂ u (G z v) := by
      have hcoords (a : TargetModel) : (e ⟨c.symm z, e.symmL ℂ (c.symm z) a⟩).2 = a := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 a
      rw [k.pairing_eq_gramMatrix e _ hz.2, hcoords u, hcoords v, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j, conj (u i) * k.gramMatrix e (c.symm z) i j * v j) =
        (∑ j, k.gramMatrix e (c.symm z) i j * v j) * conj (u i)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hequiv (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) :
        ∃ L : TargetModel ≃L[ℂ] TargetModel, L.toContinuousLinearMap = G z := by
      have hinj : Function.Injective (G z) := by
        intro u v huv
        have hzG : G z (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have hzpair := hpair z hz (u - v) (u - v)
        rw [hzG, inner_zero_right] at hzpair
        have hzvec : e.symmL ℂ (c.symm z) (u - v) = 0 :=
          (k.toCore _).definite _ hzpair
        have hzcoords := congrArg (e.continuousLinearMapAt ℂ (c.symm z)) hzvec
        rw [e.continuousLinearMapAt_symmL hz.2, map_zero] at hzcoords
        exact sub_eq_zero.mp hzcoords
      exact ⟨(LinearEquiv.ofBijective (G z).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
    refine ⟨G, fun z hz ↦ (hG z hz).contDiffWithinAt, ?_, ?_⟩
    · intro z hz
      obtain ⟨L, hL⟩ := hequiv z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact (hi.comp z (hG z hz)).contDiffWithinAt
    · intro z hz
      exact ⟨hequiv z hz, hpair z hz⟩
  -- The coordinate integration formula retains the prescribed measure, not a new density.
  have hchartIntegral (c : OpenPartialHomeomorph M TModel) (μ : Measure M)
      (w : TModel → ℝ) (hw : ContinuousOn w c.target) (hpos : ∀ z ∈ c.target, 0 ≤ w z)
      (hmap : Measure.map c (μ.restrict c.source) =
        (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z)))
      (f : M → ℂ) (hf : Continuous f) (hsupp : Function.support f ⊆ c.source) :
      (∫ x, f x ∂μ) = ∫ z in c.target, w z • f (c.symm z) := by
    classical
    -- Extend the target test by zero outside the prescribed chart target.
    let g : TModel → ℂ := c.target.piecewise (fun z ↦ f (c.symm z)) (fun _ ↦ 0)
    have hg : Measurable g :=
      (hf.comp_continuousOn c.continuousOn_symm).measurable_piecewise
        continuousOn_const c.open_target.measurableSet
    have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
      ENNReal.continuous_ofReal.continuousOn.comp hw (Set.mapsTo_univ _ _)
        |>.aemeasurable c.open_target.measurableSet
    calc
      (∫ x, f x ∂μ) = ∫ x in c.source, f x ∂μ := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ Function.notMem_support.mp (fun h ↦ hx (hsupp h)))
      _ = ∫ x in c.source, g (c x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
        simp [g, Set.piecewise_eq_of_mem, c.map_source hx, c.left_inv hx]
      _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
        (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet)
          hg.aestronglyMeasurable).symm
      _ = ∫ z in c.target, (ENNReal.ofReal (w z)).toReal • g z := by
        rw [hmap]
        exact integral_withDensity_eq_integral_toReal_smul₀ hwmeas
          (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
      _ = ∫ z in c.target, w z • f (c.symm z) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
        simp [g, Set.piecewise_eq_of_mem, hz, ENNReal.toReal_ofReal (hpos z hz)]
  -- Gram conjugation converts the existing scalar-density adjoint into the metric adjoint.
  have hmetricLocal {U : Set TModel} (hU : IsOpen U)
      (w : TModel → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hpos : ∀ x ∈ U, 0 < w x)
      (P : CoordinateDifferentialOperator n r q d U)
      (G Gi : TModel → (SourceModel →L[ℂ] SourceModel))
      (H : TModel → (TargetModel →L[ℂ] TargetModel))
      (hGi : ContDiffOn ℝ ∞ Gi U) (hH : ContDiffOn ℝ ∞ H U)
      (hGinv : ∀ x ∈ U, ∀ u, G x (Gi x u) = u)
      (hHerm : ∀ x ∈ U, ∀ v z, inner ℂ (H x v) z = inner ℂ v (H x z)) :
      ∃ Q : CoordinateDifferentialOperator n q r d U,
        ∀ (u : 𝓢(TModel, SourceModel)) (v : 𝓢(TModel, TargetModel)),
          HasCompactSupport u → tsupport u ⊆ U →
          HasCompactSupport v → tsupport v ⊆ U →
            (∫ x, w x • inner ℂ (P.apply u x) (H x (v x))) =
              ∫ x, w x • inner ℂ (u x) (G x (Q.apply v x)) := by
    classical
    -- Apply the original scalar-density theorem to the Gram-weighted output coefficients.
    have hcomp {a b c : ℕ} :
        ContDiff ℝ ∞ (fun z :
          ((EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin c)) ×
            (EuclideanSpace ℂ (Fin a) →L[ℂ] EuclideanSpace ℂ (Fin b))) ↦ z.1.comp z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
    let PH : CoordinateDifferentialOperator n r q d U :=
      { coefficient := fun k α x ↦ (H x).comp (P.coefficient k α x)
        smooth_coefficient := fun k α ↦
          hcomp.comp_contDiffOn (hH.prodMk (P.smooth_coefficient k α)) }
    have hPH (u : TModel → SourceModel) (x : TModel) : PH.apply u x = H x (P.apply u x) := by
      simp [CoordinateDifferentialOperator.apply, PH, map_sum]
      rfl
    obtain ⟨R, hR⟩ := exists_formalAdjoint hU w hw hpos PH
    let Q : CoordinateDifferentialOperator n q r d U :=
      { coefficient := fun k α x ↦ (Gi x).comp (R.coefficient k α x)
        smooth_coefficient := fun k α ↦
          hcomp.comp_contDiffOn (hGi.prodMk (R.smooth_coefficient k α)) }
    have hQ (v : TModel → TargetModel) (x : TModel) : Q.apply v x = Gi x (R.apply v x) := by
      simp [CoordinateDifferentialOperator.apply, Q, map_sum]
      rfl
    refine ⟨Q, ?_⟩
    intro u v hu huU hv hvU
    -- The inverse source Gram matrix is used only where the compact tests can be nonzero.
    calc
      (∫ x, w x • inner ℂ (P.apply u x) (H x (v x))) =
          ∫ x, w x • inner ℂ (PH.apply u x) (v x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ U
        · rw [hPH, hHerm x hx]
        · have hvzero : v x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hvU h))
          simp [hvzero]
      _ = ∫ x, w x • inner ℂ (u x) (R.apply v x) := hR u v hu huU hv hvU
      _ = ∫ x, w x • inner ℂ (u x) (G x (Q.apply v x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ U
        · rw [hQ, hGinv x hx]
        · have huzero : u x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (huU h))
          simp [huzero]
  -- Localize and extend actual sections; the cutoff is one on the smaller chart domain.
  have hlocalAction
      (c : OpenPartialHomeomorph M TModel)
      (hc : c ∈ atlas TModel M)
      (e : Trivialization SourceModel
        (π SourceModel E)) [MemTrivializationAtlas e]
      (f : Trivialization TargetModel
        (π TargetModel F)) [MemTrivializationAtlas f]
      (U : Set M) (hU : IsOpen U)
      (D : CoordinateDifferentialOperator n r q d (c '' U))
      (hD : HasCoordinateExpression E F d P.toLinearMap c e f U D)
      (x : M) (hx : x ∈ U) :
      ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ R : smoothSections (n := n) (r := q) F →ₗ[ℂ]
            smoothSections (n := n) (r := r) E,
          (∃ D' : CoordinateDifferentialOperator n q r d (c '' V),
            HasCoordinateExpression F E d R c f e V D') ∧
          ∀ (K : Set M), IsCompact K → K ⊆ V →
            ∀ u : supportedSmoothSections (n := n) (r := r) E K,
            ∀ v : smoothSections (n := n) (r := q) F,
              k.sectionPairing μ (P.toLinearMap u.val) v = h.sectionPairing μ u.val (R v) := by
    classical
    let T := EuclideanSpace ℝ (Fin n)
    let W := EuclideanSpace ℂ (Fin r)
    let Z := EuclideanSpace ℂ (Fin q)
    have hUsource : U ⊆ c.source := fun y hy ↦ (hD.1 hy).1.1
    have hDU : IsOpen (c '' U) := c.isOpen_image_of_subset_source hU hUsource
    have hUc : c '' U ⊆ c.target := fun _ ⟨y, hy, hzy⟩ ↦ hzy ▸ c.map_source (hUsource hy)
    have hUe : c '' U ⊆ c.target ∩ c.symm ⁻¹' e.baseSet := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨c.map_source (hUsource hy), by simpa [c.left_inv (hUsource hy)] using (hD.1 hy).1.2⟩
    have hUf : c '' U ⊆ c.target ∩ c.symm ⁻¹' f.baseSet := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨c.map_source (hUsource hy), by simpa [c.left_inv (hUsource hy)] using (hD.1 hy).2⟩
    -- Keep the actual density and the two original Gram operators on this overlap.
    obtain ⟨w, hw, hwpos, hwmap⟩ := hμ.exists_smooth_density c hc
    obtain ⟨G, _, hGi, hGpair⟩ := hgramE c hc e
    obtain ⟨H, hH, _, hHpair⟩ := hgramF c hc f
    have hGinv (z : T) (hz : z ∈ c '' U) (a : W) : G z ((G z).inverse a) = a := by
      obtain ⟨L, hL⟩ := (hGpair z (hUe hz)).1
      rw [← hL, ContinuousLinearMap.inverse_equiv]
      exact L.apply_symm_apply a
    have hHerm (z : T) (hz : z ∈ c '' U) (a b : Z) :
        inner ℂ (H z a) b = inner ℂ a (H z b) := by
      have hab := (hHpair z (hUf hz)).2 a b
      have hba := (hHpair z (hUf hz)).2 b a
      calc
        inner ℂ (H z a) b = conj (inner ℂ b (H z a)) := (inner_conj_symm _ _).symm
        _ = conj (k.pairing (c.symm z) (f.symmL ℂ (c.symm z) b)
            (f.symmL ℂ (c.symm z) a)) := congrArg conj hba.symm
        _ = k.pairing (c.symm z) (f.symmL ℂ (c.symm z) a)
            (f.symmL ℂ (c.symm z) b) := (k.toCore _).conj_inner_symm _ _
        _ = inner ℂ a (H z b) := hab
    obtain ⟨Q, hQ⟩ := hmetricLocal hDU w (hw.mono hUc)
      (fun z hz ↦ hwpos z (hUc hz)) D G (fun z ↦ (G z).inverse) H
      (hGi.mono hUe) (hH.mono hUf) hGinv hHerm
    -- Choose a common cutoff which is one on an open neighborhood of the original point.
    obtain ⟨b, _, hb⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, T)) (c x)).mem_iff.mp
        (hDU.mem_nhds (Set.mem_image_of_mem c hx))
    let A : BundleChartCutoff (r := r) E c :=
      ⟨e, inferInstance, b, b.contMDiff.contDiff, b.hasCompactSupport, hb.trans hUe⟩
    let B : BundleChartCutoff (r := q) F c :=
      ⟨f, inferInstance, b, b.contMDiff.contDiff, b.hasCompactSupport, hb.trans hUf⟩
    let V := U ∩ c ⁻¹' interior {z : T | b z = 1}
    have hV : IsOpen V := by
      exact (c.continuousOn.mono hUsource).isOpen_inter_preimage hU isOpen_interior
    have hxV : x ∈ V := by
      refine ⟨hx, mem_interior_iff_mem_nhds.mpr ?_⟩
      exact b.eventuallyEq_one
    have hBV (v : smoothSections (n := n) (r := q) F) :
        ContDiff ℝ ∞ (Q.apply (B.localize hc v)) ∧
          HasCompactSupport (Q.apply (B.localize hc v)) ∧
            tsupport (Q.apply (B.localize hc v)) ⊆ tsupport (B.localize hc v) :=
      Q.apply_testFunction_properties hDU _ ((B.localize hc v).smooth ⊤)
        (B.hasCompactSupport_localizedFunction v)
        ((B.tsupport_localizedFunction_subset v).trans hb)
    let qv (v : smoothSections (n := n) (r := q) F) : 𝓢(T, W) :=
      (hBV v).2.1.toSchwartzMap (hBV v).1
    have hqadd (u v : smoothSections (n := n) (r := q) F) : qv (u + v) = qv u + qv v := by
      apply DFunLike.ext
      intro z
      change Q.apply (B.localize hc (u + v)) z =
        Q.apply (B.localize hc u) z + Q.apply (B.localize hc v) z
      rw [B.localize_add]
      change Q.apply ((fun z ↦ B.localize hc u z) + (fun z ↦ B.localize hc v z)) z = _
      simp only [CoordinateDifferentialOperator.apply,
        iteratedFDeriv_add_apply ((B.localize hc u).smooth _).contDiffAt
          ((B.localize hc v).smooth _).contDiffAt,
        add_apply, smul_add, map_add, Finset.sum_add_distrib]
    have hqsmul (a : ℂ) (v : smoothSections (n := n) (r := q) F) :
        qv (a • v) = a • qv v := by
      apply DFunLike.ext
      intro z
      change Q.apply (B.localize hc (a • v)) z = a • Q.apply (B.localize hc v) z
      rw [B.localize_smul]
      change Q.apply (a • (fun z ↦ B.localize hc v z)) z = _
      simp only [CoordinateDifferentialOperator.apply,
        iteratedFDeriv_const_smul_apply ((B.localize hc v).smooth _).contDiffAt,
        smul_apply, smul_comm _ a, map_smul, Finset.smul_sum]
    let qmap : smoothSections (n := n) (r := q) F →ₗ[ℂ] 𝓢(T, W) :=
      { toFun := qv
        map_add' := hqadd
        map_smul' := fun a v ↦ hqsmul a v }
    let R : smoothSections (n := n) (r := q) F →ₗ[ℂ]
        smoothSections (n := n) (r := r) E := (A.extendLinearMap hc).comp qmap
    refine ⟨V, hV, hxV, Set.inter_subset_left, R, ?_, ?_⟩
    · let Q' : CoordinateDifferentialOperator n q r d (c '' V) :=
        { coefficient := Q.coefficient
          smooth_coefficient := fun j α ↦ (Q.smooth_coefficient j α).mono
            (Set.image_mono Set.inter_subset_left) }
      refine ⟨Q', (fun y hy ↦ ⟨⟨(hD.1 hy.1).1.1, (hD.1 hy.1).2⟩,
        (hD.1 hy.1).1.2⟩), ?_⟩
      intro v y hy
      have hyc := hUsource hy.1
      have hye := (hD.1 hy.1).1.2
      have hby : b (c y) = 1 := interior_subset (s := {z : T | b z = 1}) hy.2
      have hgerm : (fun z ↦ B.localize hc v z) =ᶠ[𝓝 (c y)] sectionInChart F c f v.val := by
        filter_upwards [isOpen_interior.mem_nhds hy.2,
          c.open_target.mem_nhds (c.map_source hyc)] with z hz hzt
        have hbz : b z = 1 := interior_subset (s := {z : T | b z = 1}) hz
        change (if z ∈ c.target then (b z : ℂ) • sectionInChart F c f v.val z else 0) = _
        rw [ite_eq_left hzt, hbz, Complex.ofReal_one, one_smul]
      change (e ⟨y, A.extendedFunction (qv v) y⟩).2 = Q'.apply _ (c y)
      simp only [BundleChartCutoff.extendedFunction, A, ite_eq_left hyc, hby,
        Complex.ofReal_one, one_smul]
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hye, e.continuousLinearMapAt_symmL hye]
      change Q.apply (B.localize hc v) (c y) = Q.apply _ (c y)
      simp only [CoordinateDifferentialOperator.apply]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro α _
      rw [(hgerm.iteratedFDeriv ℝ j.val).eq_of_nhds]
    · intro K hK hKV u v
      let a := A.localize hc u.val
      let z := B.localize hc v
      have hKU : K ⊆ U := hKV.trans Set.inter_subset_left
      have hKsource : K ⊆ c.source := hKU.trans hUsource
      have hKc : IsCompact (c '' K) := hK.image_of_continuousOn (c.continuousOn.mono hKsource)
      have hPu (y : M) (hy : y ∉ K) : (P.toLinearMap u.val).val y = 0 := by
        have hgerm : ∀ᶠ t in 𝓝 y, u.val.val t = (0 : E t) := by
          filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hy] with t ht
          exact u.property t ht
        simpa using P.apply_eq_of_eventually_eq u.val 0 y hgerm
      have hasupp : tsupport a ⊆ c '' K := by
        apply closure_minimal ?_ hKc.isClosed
        intro t ht
        have htb : t ∈ tsupport b := A.tsupport_localizedFunction_subset u.val
          (subset_tsupport _ ht)
        have htt := (hUe (hb htb)).1
        have hte := (hUe (hb htb)).2
        refine ⟨c.symm t, ?_, c.right_inv htt⟩
        by_contra htk
        apply ht
        change (if t ∈ c.target then (b t : ℂ) •
          (e ⟨c.symm t, u.val.val (c.symm t)⟩).2 else 0) = 0
        rw [ite_eq_left htt, u.property _ htk, ← e.continuousLinearMapAt_apply_of_mem ℂ hte,
          map_zero, smul_zero]
      have ha (t : T) (ht : t ∈ c '' U) : a t = sectionInChart E c e u.val.val t := by
        obtain ⟨y, hy, rfl⟩ := ht
        have hyc := hUsource hy
        have hye := (hD.1 hy).1.2
        change (if c y ∈ c.target then (b (c y) : ℂ) •
          sectionInChart E c e u.val.val (c y) else 0) = _
        rw [ite_eq_left (c.map_source hyc)]
        by_cases hyK : y ∈ K
        · have hby : b (c y) = 1 := interior_subset (s := {z : T | b z = 1}) (hKV hyK).2
          rw [hby, Complex.ofReal_one, one_smul]
        · have hzero : sectionInChart E c e u.val.val (c y) = 0 := by
            unfold sectionInChart
            rw [c.left_inv hyc, u.property y hyK,
              ← e.continuousLinearMapAt_apply_of_mem ℂ hye, map_zero]
          rw [hzero, smul_zero]
      have hDP (y : M) (hy : y ∈ U) :
          (f ⟨y, (P.toLinearMap u.val).val y⟩).2 = D.apply a (c y) := by
        rw [hD.2 u.val y hy]
        have hgerm : (fun t ↦ a t) =ᶠ[𝓝 (c y)] sectionInChart E c e u.val.val := by
          filter_upwards [hDU.mem_nhds (Set.mem_image_of_mem c hy)] with t ht
          exact ha t ht
        simp only [CoordinateDifferentialOperator.apply]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro α _
        rw [(hgerm.iteratedFDeriv ℝ j.val).eq_of_nhds]
      have hDa := D.apply_testFunction_properties hDU a (a.smooth ⊤)
        (A.hasCompactSupport_localizedFunction u.val)
        (hasupp.trans (Set.image_mono hKU))
      have hDaK : tsupport (D.apply a) ⊆ c '' K := hDa.2.2.trans hasupp
      have hleft (t : T) (ht : t ∈ c.target) :
          k.pairing (c.symm t) ((P.toLinearMap u.val).val (c.symm t)) (v.val (c.symm t)) =
            inner ℂ (D.apply a t) (H t (z t)) := by
        by_cases hyK : c.symm t ∈ K
        · have hyU := hKU hyK
          have htf := (hD.1 hyU).2
          have htu : t ∈ c '' U := ⟨c.symm t, hyU, c.right_inv ht⟩
          have hbt : b t = 1 := by simpa [c.right_inv ht] using
            (show b (c (c.symm t)) = 1 from interior_subset (s := {z : T | b z = 1}) (hKV hyK).2)
          have hz : z t = (f ⟨c.symm t, v.val (c.symm t)⟩).2 := by
            change (if t ∈ c.target then (b t : ℂ) •
              (f ⟨c.symm t, v.val (c.symm t)⟩).2 else 0) = _
            rw [ite_eq_left ht, hbt, Complex.ofReal_one, one_smul]
          have hp := (hHpair t (hUf htu)).2
            (f.continuousLinearMapAt ℂ (c.symm t) ((P.toLinearMap u.val).val (c.symm t)))
            (f.continuousLinearMapAt ℂ (c.symm t) (v.val (c.symm t)))
          rw [f.symmL_continuousLinearMapAt htf, f.symmL_continuousLinearMapAt htf] at hp
          rw [hp, hz, f.continuousLinearMapAt_apply_of_mem ℂ htf,
            f.continuousLinearMapAt_apply_of_mem ℂ htf, hDP _ hyU, c.right_inv ht]
        · have hnot : t ∉ c '' K := by
            rintro ⟨y, hy, hyt⟩
            apply hyK
            rw [← hyt, c.left_inv (hKsource hy)]
            exact hy
          have hzero := image_eq_zero_of_notMem_tsupport (fun h ↦ hnot (hDaK h))
          rw [hPu _ hyK, hzero, inner_zero_left]
          let : InnerProductSpace.Core ℂ (F (c.symm t)) := k.toCore _
          exact InnerProductSpace.Core.inner_zero_left _
      have hright (t : T) (ht : t ∈ c.target) :
          h.pairing (c.symm t) (u.val.val (c.symm t)) ((R v).val (c.symm t)) =
            inner ℂ (a t) (G t (Q.apply z t)) := by
        by_cases hyK : c.symm t ∈ K
        · have hyU := hKU hyK
          have hte := (hD.1 hyU).1.2
          have htu : t ∈ c '' U := ⟨c.symm t, hyU, c.right_inv ht⟩
          have hbt : b t = 1 := by simpa [c.right_inv ht] using
            (show b (c (c.symm t)) = 1 from interior_subset (s := {z : T | b z = 1}) (hKV hyK).2)
          have hRval : (R v).val (c.symm t) = e.symmL ℂ (c.symm t) (Q.apply z t) := by
            change A.extendedFunction (qv v) (c.symm t) = _
            simp only [BundleChartCutoff.extendedFunction, A, ite_eq_left (c.map_target ht),
              c.right_inv ht, hbt, Complex.ofReal_one, one_smul]
            rfl
          have hp := (hGpair t (hUe htu)).2
            (e.continuousLinearMapAt ℂ (c.symm t) (u.val.val (c.symm t))) (Q.apply z t)
          rw [e.symmL_continuousLinearMapAt hte] at hp
          rw [hRval, hp, e.continuousLinearMapAt_apply_of_mem ℂ hte, ha t htu]
          rfl
        · have hnot : t ∉ c '' K := by
            rintro ⟨y, hy, hyt⟩
            apply hyK
            rw [← hyt, c.left_inv (hKsource hy)]
            exact hy
          have hzero := image_eq_zero_of_notMem_tsupport (fun h ↦ hnot (hasupp h))
          rw [u.property _ hyK, hzero, inner_zero_left]
          let : InnerProductSpace.Core ℂ (E (c.symm t)) := h.toCore _
          exact InnerProductSpace.Core.inner_zero_left _
      have htransportLeft : k.sectionPairing μ (P.toLinearMap u.val) v =
          ∫ t, w t • inner ℂ (D.apply a t) (H t (z t)) := by
        rw [SmoothHermitianMetric.sectionPairing]
        rw [hchartIntegral c μ w hw.continuousOn (fun t ht ↦ (hwpos t ht).le) hwmap
          _ (k.contMDiff_pairing (P.toLinearMap u.val) v).continuous (by
            intro y hy
            by_contra hyc
            have hyK : y ∉ K := fun h ↦ hyc (hKsource h)
            apply hy
            change k.pairing y ((P.toLinearMap u.val).val y) (v.val y) = 0
            rw [hPu y hyK]
            let : InnerProductSpace.Core ℂ (F y) := k.toCore y
            exact InnerProductSpace.Core.inner_zero_left _)]
        calc
          _ = ∫ t in c.target, w t • inner ℂ (D.apply a t) (H t (z t)) := by
            apply setIntegral_congr_fun c.open_target.measurableSet
            intro t ht
            exact congrArg (fun a : ℂ ↦ w t • a) (hleft t ht)
          _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
            intro t ht
            have hzero := image_eq_zero_of_notMem_tsupport
              (fun h ↦ ht (hUc ((Set.image_mono hKU) (hDaK h))))
            rw [hzero, inner_zero_left, smul_zero])
      have htransportRight : h.sectionPairing μ u.val (R v) =
          ∫ t, w t • inner ℂ (a t) (G t (Q.apply z t)) := by
        rw [SmoothHermitianMetric.sectionPairing]
        rw [hchartIntegral c μ w hw.continuousOn (fun t ht ↦ (hwpos t ht).le) hwmap
          _ (h.contMDiff_pairing u.val (R v)).continuous (by
            intro y hy
            by_contra hyc
            have hyK : y ∉ K := fun h ↦ hyc (hKsource h)
            apply hy
            change h.pairing y (u.val.val y) ((R v).val y) = 0
            rw [u.property y hyK]
            let : InnerProductSpace.Core ℂ (E y) := h.toCore y
            exact InnerProductSpace.Core.inner_zero_left _)]
        calc
          _ = ∫ t in c.target, w t • inner ℂ (a t) (G t (Q.apply z t)) := by
            apply setIntegral_congr_fun c.open_target.measurableSet
            intro t ht
            exact congrArg (fun a : ℂ ↦ w t • a) (hright t ht)
          _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
            intro t ht
            have hzero := image_eq_zero_of_notMem_tsupport
              (fun h ↦ ht (hUc ((Set.image_mono hKU) (hasupp h))))
            rw [hzero, inner_zero_left, smul_zero])
      rw [htransportLeft, htransportRight]
      exact hQ a z (A.hasCompactSupport_localizedFunction u.val)
        (hasupp.trans (Set.image_mono hKU)) (B.hasCompactSupport_localizedFunction v)
        ((B.tsupport_localizedFunction_subset v).trans hb)
  -- Equal local test pairings glue the actions and certify every original chart.
  have hexists :
      ∃ Q : DifferentialOperator (n := n) (r := q) (q := r) F E d,
        IsCompactTestMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap := by
    classical
    -- The common local testing condition separates the values of two smooth candidate outputs.
    let LocalPair (V : Set M)
        (R : smoothSections (n := n) (r := q) F →ₗ[ℂ]
          smoothSections (n := n) (r := r) E) : Prop :=
      ∀ (K : Set M), IsCompact K → K ⊆ V →
        ∀ u : supportedSmoothSections (n := n) (r := r) E K,
        ∀ v : smoothSections (n := n) (r := q) F,
          k.sectionPairing μ (P.toLinearMap u.val) v = h.sectionPairing μ u.val (R v)
    have heq (V W : Set M) (hV : IsOpen V) (hW : IsOpen W)
        (R S : smoothSections (n := n) (r := q) F →ₗ[ℂ]
          smoothSections (n := n) (r := r) E)
        (hR : LocalPair V R) (hS : LocalPair W S)
        (v : smoothSections (n := n) (r := q) F) (x : M) (hxV : x ∈ V) (hxW : x ∈ W) :
        (R v).val x = (S v).val x := by
      obtain ⟨b, _, hb⟩ :=
        (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x).mem_iff.mp
          ((hV.inter hW).mem_nhds ⟨hxV, hxW⟩)
      let δ := R v - S v
      let t : supportedSmoothSections (n := n) (r := r) E (tsupport b) :=
        ⟨smoothSectionMul E (fun y ↦ (b y : ℂ))
          (Complex.ofRealCLM.contMDiff.comp b.contMDiff) δ, fun y hy ↦ by
          change (b y : ℂ) • δ.val y = 0
          rw [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_smul]⟩
      let u : supportedSmoothSections (n := n) (r := r) E (tsupport b) :=
        ⟨smoothSectionMul E (fun y ↦ (b y : ℂ))
          (Complex.ofRealCLM.contMDiff.comp b.contMDiff) t.val, fun y hy ↦ by
          change (b y : ℂ) • t.val.val y = 0
          rw [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_smul]⟩
      have hpair := (hR _ b.hasCompactSupport (hb.trans Set.inter_subset_left) u v).symm.trans
        (hS _ b.hasCompactSupport (hb.trans Set.inter_subset_right) u v)
      have hzero : h.sectionPairing μ u.val δ = 0 := by
        change (∫ y, h.pairing y (u.val.val y) ((R v).val y - (S v).val y) ∂μ) = 0
        have hsub (y : M) : h.pairing y (u.val.val y) ((R v).val y - (S v).val y) =
            h.pairing y (u.val.val y) ((R v).val y) -
              h.pairing y (u.val.val y) ((S v).val y) := by
          let : InnerProductSpace.Core ℂ (E y) := h.toCore y
          exact InnerProductSpace.Core.inner_sub_right _ _ _
        simp_rw [hsub]
        rw [integral_sub (h.integrable_pairing_of_supported μ _ b.hasCompactSupport u _)
          (h.integrable_pairing_of_supported μ _ b.hasCompactSupport u _), sub_eq_zero]
        exact hpair
      have htzero : h.sectionPairing μ t.val t.val = 0 := by
        rw [← hzero]
        apply integral_congr_ae
        filter_upwards [] with y
        change (h.toCore y).inner ((b y : ℂ) • δ.val y) ((b y : ℂ) • δ.val y) =
          (h.toCore y).inner ((b y : ℂ) • ((b y : ℂ) • δ.val y)) (δ.val y)
        let : InnerProductSpace.Core ℂ (E y) := h.toCore y
        rw [InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right,
          InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_left]
        simp only [Complex.conj_ofReal]
      have ht :=
        (h.sectionPairing_self_eq_zero_iff_of_supported μ _ b.hasCompactSupport t).mp htzero
      have htx := congrArg (fun z : supportedSmoothSections (n := n) (r := r) E (tsupport b) ↦
        z.val.val x) ht
      change (b x : ℂ) • ((R v).val x - (S v).val x) = 0 at htx
      rw [b.eq_one, Complex.ofReal_one, one_smul] at htx
      exact sub_eq_zero.mp htx
    -- Each arbitrary original chart/frame pair has one such local adjoint action.
    have hlocal (c : OpenPartialHomeomorph M TModel)
        (hc : c ∈ atlas TModel M)
        (e : Trivialization SourceModel
          (π SourceModel E)) [MemTrivializationAtlas e]
        (f : Trivialization TargetModel
          (π TargetModel F)) [MemTrivializationAtlas f]
        (x : M) (hx : x ∈ c.source ∩ e.baseSet ∩ f.baseSet) :
        ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
          ∃ R : smoothSections (n := n) (r := q) F →ₗ[ℂ]
            smoothSections (n := n) (r := r) E,
            LocalPair V R ∧ ∃ Q : CoordinateDifferentialOperator n q r d (c '' V),
              HasCoordinateExpression F E d R c f e V Q := by
      obtain ⟨U, hU, hxU, D, hD⟩ := P.isDifferentialOperator c hc e f x hx
      obtain ⟨V, hV, hxV, _, R, hcoord, hpair⟩ :=
        hlocalAction c hc e f U hU D hD x hxU
      exact ⟨V, hV, hxV, R, hpair, hcoord⟩
    have hcover (x : M) :
        ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
          ∃ R : smoothSections (n := n) (r := q) F →ₗ[ℂ]
            smoothSections (n := n) (r := r) E, LocalPair V R := by
      obtain ⟨V, hV, hxV, R, hR, _⟩ := hlocal
        (chartAt TModel x) (chart_mem_atlas _ x)
        (trivializationAt SourceModel E x)
        (trivializationAt TargetModel F x) x
        ⟨⟨mem_chart_source _ x, mem_baseSet_trivializationAt _ _ x⟩,
          mem_baseSet_trivializationAt _ _ x⟩
      exact ⟨V, hV, hxV, R, hR⟩
    choose V hV hxV R hR using hcover
    -- Choose the common value at each point. On every covering open set this is a smooth R x.
    let qv (v : smoothSections (n := n) (r := q) F) (x : M) : E x := (R x v).val x
    have hqv (v : smoothSections (n := n) (r := q) F) (x y : M) (hy : y ∈ V x) :
        qv v y = (R x v).val y := heq (V y) (V x) (hV y) (hV x)
          (R y) (R x) (hR y) (hR x) v y (hxV y) hy
    have hsmooth (v : smoothSections (n := n) (r := q) F) :
        IsSmoothSection (n := n) (r := r) E (qv v) := by
      intro e he x hx
      have hnear := ((R x v).property e he).contMDiffAt (e.open_baseSet.mem_nhds hx)
      apply (hnear.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [(hV x).mem_nhds (hxV x)] with y hy
      rw [hqv v x y hy]
    let qmap : smoothSections (n := n) (r := q) F →ₗ[ℂ]
        smoothSections (n := n) (r := r) E :=
      { toFun v := ⟨qv v, hsmooth v⟩
        map_add' v w := by
          apply Subtype.ext
          funext x
          change (R x (v + w)).val x = (R x v).val x + (R x w).val x
          exact congrArg (fun s : smoothSections (n := n) (r := r) E ↦ s.val x)
            ((R x).map_add v w)
        map_smul' a v := by
          apply Subtype.ext
          funext x
          change (R x (a • v)).val x = a • (R x v).val x
          exact congrArg (fun s : smoothSections (n := n) (r := r) E ↦ s.val x)
            ((R x).map_smul a v) }
    have hdiff : IsDifferentialOperator F E d qmap := by
      intro c hc f hf e he x hx
      obtain ⟨W, hW, hxW, S, hS, D, hD⟩ := hlocal c hc e f x ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
      refine ⟨W, hW, hxW, D, hD.1, ?_⟩
      intro v y hy
      have hv : qv v y = (S v).val y :=
        heq (V y) W (hV y) hW (R y) S (hR y) hS v y (hxV y) hy
      change (e ⟨y, qv v y⟩).2 = _
      rw [hv]
      exact hD.2 v y hy
    let Q : DifferentialOperator (n := n) (r := q) (q := r) F E d := ⟨qmap, hdiff⟩
    refine ⟨Q, ?_⟩
    intro K L hK _ u v
    -- A finite partition on the compact input support reduces the global identity to the charts.
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace TModel M
    obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hxV x⟩)
    have hscover : K ⊆ ⋃ i : s, V i.val := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) hK.isClosed (fun i : s ↦ V i.val)
      (fun i ↦ hV i.val) hscover
    let K' (i : s) := K ∩ tsupport (ρ i)
    have hK' (i : s) : IsCompact (K' i) := hK.inter_right (isClosed_tsupport (ρ i))
    have hK'V (i : s) : K' i ⊆ V i.val := fun _ hx ↦ hρ i hx.2
    let u' (i : s) : supportedSmoothSections (n := n) (r := r) E (K' i) :=
      ⟨smoothSectionMul E (fun x ↦ (ρ i x : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (ρ i).contMDiff) u.val, fun x hx ↦ by
        change (ρ i x : ℂ) • u.val.val x = 0
        by_cases hxK : x ∈ K
        · have hxρ : x ∉ tsupport (ρ i) := fun h ↦ hx ⟨hxK, h⟩
          rw [image_eq_zero_of_notMem_tsupport hxρ, Complex.ofReal_zero, zero_smul]
        · rw [u.property x hxK, smul_zero]⟩
    have hsum : ∑ i : s, (u' i).val = u.val := by
      apply Subtype.ext
      funext x
      simp only [Submodule.coe_sum, Finset.sum_apply]
      change (∑ i : s, (ρ i x : ℂ) • u.val.val x) = u.val.val x
      rw [← Finset.sum_smul, ← Complex.ofReal_sum]
      by_cases hx : x ∈ K
      · have hρsum := ρ.sum_eq_one hx
        rw [finsum_eq_sum_of_fintype] at hρsum
        rw [hρsum, Complex.ofReal_one, one_smul]
      · rw [u.property x hx, smul_zero]
    let Pu' (i : s) : supportedSmoothSections (n := n) (r := q) F (K' i) :=
      ⟨P.toLinearMap (u' i).val, fun x hx ↦ by
        have hgerm : ∀ᶠ y in 𝓝 x, (u' i).val.val y = (0 : E y) := by
          filter_upwards [(hK' i).isClosed.isOpen_compl.mem_nhds hx] with y hy
          exact (u' i).property y hy
        simpa using P.apply_eq_of_eventually_eq (u' i).val 0 x hgerm⟩
    have hleftsum : k.sectionPairing μ (P.toLinearMap u.val) v.val =
        ∑ i : s, k.sectionPairing μ (Pu' i).val v.val := by
      have hsumP : P.toLinearMap u.val = ∑ i : s, (Pu' i).val := by
        rw [← hsum, map_sum]
      rw [hsumP]
      unfold SmoothHermitianMetric.sectionPairing
      have hpoint (x : M) : k.pairing x ((∑ i : s, (Pu' i).val).val x) (v.val.val x) =
          ∑ i : s, k.pairing x ((Pu' i).val.val x) (v.val.val x) := by
        let : InnerProductSpace.Core ℂ (F x) := k.toCore x
        let f : F x →+ ℂ :=
          { toFun := fun a ↦ k.pairing x a (v.val.val x)
            map_zero' := InnerProductSpace.Core.inner_zero_left _
            map_add' := fun a b ↦ (k.toCore x).add_left a b _ }
        simp only [Submodule.coe_sum, Finset.sum_apply]
        change f (∑ i : s, (Pu' i).val.val x) = ∑ i : s, f ((Pu' i).val.val x)
        exact map_sum f (fun i : s ↦ (Pu' i).val.val x) Finset.univ
      simp_rw [hpoint]
      exact integral_finsetSum _ (fun i _ ↦
        k.integrable_pairing_of_supported μ (K' i) (hK' i) (Pu' i) v.val)
    have hrightsum : h.sectionPairing μ u.val (Q.toLinearMap v.val) =
        ∑ i : s, h.sectionPairing μ (u' i).val (Q.toLinearMap v.val) := by
      conv_lhs => rw [← hsum]
      unfold SmoothHermitianMetric.sectionPairing
      have hpoint (x : M) :
          h.pairing x ((∑ i : s, (u' i).val).val x) ((Q.toLinearMap v.val).val x) =
            ∑ i : s, h.pairing x ((u' i).val.val x) ((Q.toLinearMap v.val).val x) := by
        let : InnerProductSpace.Core ℂ (E x) := h.toCore x
        let f : E x →+ ℂ :=
          { toFun := fun a ↦ h.pairing x a ((Q.toLinearMap v.val).val x)
            map_zero' := InnerProductSpace.Core.inner_zero_left _
            map_add' := fun a b ↦ (h.toCore x).add_left a b _ }
        simp only [Submodule.coe_sum, Finset.sum_apply]
        change f (∑ i : s, (u' i).val.val x) = ∑ i : s, f ((u' i).val.val x)
        exact map_sum f (fun i : s ↦ (u' i).val.val x) Finset.univ
      simp_rw [hpoint]
      exact integral_finsetSum _ (fun i _ ↦
        h.integrable_pairing_of_supported μ (K' i) (hK' i) (u' i) (Q.toLinearMap v.val))
    rw [hleftsum, hrightsum]
    apply Finset.sum_congr rfl
    intro i _
    change k.sectionPairing μ (P.toLinearMap (u' i).val) v.val = _
    rw [hR i.val (K' i) (hK' i) (hK'V i) (u' i) v.val]
    apply integral_congr_ae
    filter_upwards [] with x
    change h.pairing x ((u' i).val.val x) ((R i.val v.val).val x) =
      h.pairing x ((u' i).val.val x) (qv v.val x)
    by_cases hx : x ∈ K' i
    · rw [hqv v.val i.val x (hK'V i hx)]
    · rw [(u' i).property x hx]
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      change (h.toCore x).inner 0 ((R i.val v.val).val x) = (h.toCore x).inner 0 (qv v.val x)
      rw [InnerProductSpace.Core.inner_zero_left, InnerProductSpace.Core.inner_zero_left]
  -- Compact tests determine every input germ, hence the complete section action.
  have hunique
      (Q R : DifferentialOperator (n := n) (r := q) (q := r) F E d)
      (hQ : IsCompactTestMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap)
      (hR : IsCompactTestMetricFormalAdjoint h k μ P.toLinearMap R.toLinearMap) : Q = R := by
    classical
    -- Locality makes both images of a supported input vanish off that same closed support.
    have hpreserve (T : DifferentialOperator (n := n) (r := q) (q := r) F E d)
        (L : Set M) (hL : IsClosed L)
        (v : supportedSmoothSections (n := n) (r := q) F L) :
        ∀ x, x ∉ L → (T.toLinearMap v.val).val x = 0 := by
      intro x hx
      have hgerm : ∀ᶠ y in 𝓝 x, v.val.val y = (0 : F y) := by
        filter_upwards [hL.isOpen_compl.mem_nhds hx] with y hy
        exact v.property y hy
      simpa using T.apply_eq_of_eventually_eq v.val 0 x hgerm
    have hcompact (L : Set M) (hL : IsCompact L)
        (v : supportedSmoothSections (n := n) (r := q) F L) :
        Q.toLinearMap v.val = R.toLinearMap v.val := by
      let u : supportedSmoothSections (n := n) (r := r) E L :=
        ⟨Q.toLinearMap v.val - R.toLinearMap v.val, fun x hx ↦ by
          change (Q.toLinearMap v.val).val x - (R.toLinearMap v.val).val x = 0
          rw [hpreserve Q L hL.isClosed v x hx, hpreserve R L hL.isClosed v x hx, sub_self]⟩
      have heq := (hQ L L hL hL u v).symm.trans (hR L L hL hL u v)
      have hzero : h.sectionPairing μ u.val u.val = 0 := by
        change (∫ x, h.pairing x (u.val.val x)
          ((Q.toLinearMap v.val).val x - (R.toLinearMap v.val).val x) ∂μ) = 0
        have hsub (x : M) : h.pairing x (u.val.val x)
            ((Q.toLinearMap v.val).val x - (R.toLinearMap v.val).val x) =
            h.pairing x (u.val.val x) ((Q.toLinearMap v.val).val x) -
              h.pairing x (u.val.val x) ((R.toLinearMap v.val).val x) := by
          let : InnerProductSpace.Core ℂ (E x) := h.toCore x
          exact InnerProductSpace.Core.inner_sub_right _ _ _
        simp_rw [hsub]
        rw [integral_sub (h.integrable_pairing_of_supported μ L hL u _)
          (h.integrable_pairing_of_supported μ L hL u _), sub_eq_zero]
        exact heq
      have hu := (h.sectionPairing_self_eq_zero_iff_of_supported μ L hL u).mp hzero
      exact sub_eq_zero.mp (congrArg Subtype.val hu)
    -- A compact bump preserves the input germ at each point, so equality extends globally.
    have hmaps : Q.toLinearMap = R.toLinearMap := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      funext x
      let b : SmoothBumpFunction 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x :=
        Classical.choice inferInstance
      let v' : supportedSmoothSections (n := n) (r := q) F (tsupport b) :=
        ⟨smoothSectionMul F (fun y ↦ (b y : ℂ))
          (Complex.ofRealCLM.contMDiff.comp b.contMDiff) v, fun y hy ↦ by
          change (b y : ℂ) • v.val y = 0
          rw [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_smul]⟩
      have hgerm : ∀ᶠ y in 𝓝 x, v'.val.val y = v.val y := by
        filter_upwards [b.eventuallyEq_one] with y hy
        change (b y : ℂ) • v.val y = v.val y
        simp only [hy, Pi.one_apply, Complex.ofReal_one, one_smul]
      calc
        (Q.toLinearMap v).val x = (Q.toLinearMap v'.val).val x :=
          (Q.apply_eq_of_eventually_eq v'.val v x hgerm).symm
        _ = (R.toLinearMap v'.val).val x := congrArg (fun w ↦ w.val x)
          (hcompact (tsupport b) b.hasCompactSupport v')
        _ = (R.toLinearMap v).val x := R.apply_eq_of_eventually_eq v'.val v x hgerm
    cases Q
    cases R
    cases hmaps
    rfl
  obtain ⟨Q, hQ⟩ := hexists
  exact ⟨Q, hQ, fun R hR ↦ hunique R Q hR hQ⟩

/-- The original-section differential adjoint selected by its unique compact-test identity. -/
def compactTestMetricFormalAdjoint :
    DifferentialOperator (n := n) (r := q) (q := r) F E d :=
  Classical.choose (P.existsUnique_compactTestMetricFormalAdjoint (μ := μ) h k).exists

/-- The selected differential adjoint satisfies the same compact-test identity with the
original two metrics, density, and section maps. -/
theorem isCompactTestMetricFormalAdjoint_compactTestMetricFormalAdjoint :
    IsCompactTestMetricFormalAdjoint h k μ P.toLinearMap
      (P.compactTestMetricFormalAdjoint (μ := μ) h k).toLinearMap := by
  /- Apply the property of the unique witness used by the definition.
  Its identity is quantified over the specified compact supports and the
  actual section maps; no arbitrary smooth sections are inserted into a
  potentially divergent integral, and no Hilbert-space adjoint replaces
  this differential operator. -/
  exact (P.existsUnique_compactTestMetricFormalAdjoint (μ := μ) h k).exists.choose_spec

end DifferentialOperator

end AtiyahSinger
