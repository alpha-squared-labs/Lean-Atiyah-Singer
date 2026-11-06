/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateOperator
public import AtiyahSinger.Geometry.ComplexBundle
public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Order.Preorder.Finite

/-!
# Global differential operators, principal symbols and the analytic index

Public module ID: M0668.

An operator acts on global smooth sections. In manifold and bundle charts its
action agrees locally with finite differential expressions, with convention
D_j = -i ∂_j. The principal symbol is obtained from these expressions through its
existence and uniqueness theorem.

The base is a real smooth manifold without boundary, with Hausdorff and second
countable hypotheses where localization of smooth sections is needed. The bundles
have fixed complex ranks. Compactness is imposed in the index statements.
Pseudodifferential and Sobolev realizations are developed in separate modules.

Sources: Spin Geometry III.1.1–1.3, III.5 and III.13; the fixed Wikipedia
Atiyah-Singer snapshot. The smooth cokernel is a quotient of global smooth sections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- A section written in a manifold chart and a complex bundle trivialization.
The formula is total, but differential expressions use it only inside the chart overlap. -/
def sectionInChart (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) (s : ∀ x, E x) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r) :=
  fun z ↦ (e ⟨c.symm z, s (c.symm z)⟩).2

/-- The local coordinate expression of a real cotangent vector.
It is the covector pulled back by the inverse manifold chart. -/
def covectorInChart (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j ↦
    ξ ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm (c x)) (EuclideanSpace.single j 1))

/-- A finite coordinate expression represents the global operator on an open overlap. -/
def HasCoordinateExpression (m : ℕ)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    (U : Set M) (Q : CoordinateDifferentialOperator n r q m (c '' U)) : Prop :=
  U ⊆ c.source ∩ e.baseSet ∩ f.baseSet ∧
    ∀ (s : smoothSections (n := n) (r := r) E) (x : M), x ∈ U →
      (f ⟨x, (P s).val x⟩).2 = Q.apply (sectionInChart E c e s.val) (c x)

/-- The usual local definition of a global differential operator of order at most m. -/
def IsDifferentialOperator (m : ℕ)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F) : Prop :=
  ∀ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
          (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e],
        ∀ (f : Trivialization (EuclideanSpace ℂ (Fin q))
            (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f],
          ∀ x ∈ c.source ∩ e.baseSet ∩ f.baseSet,
            ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
              ∃ Q : CoordinateDifferentialOperator n r q m (c '' U),
                HasCoordinateExpression E F m P c e f U Q

/-- A global differential operator, consisting of its section action and local finite order. -/
structure DifferentialOperator (m : ℕ) where
  /-- The actual complex-linear map between global smooth section spaces. -/
  toLinearMap : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F
  /-- In local coordinates this map has a smooth finite differential expression. -/
  isDifferentialOperator : IsDifferentialOperator E F m toLinearMap

/-- The local polynomial identities characterizing the global principal symbol.
The covector transforms by the inverse chart derivative and the fibers by bundle charts. -/
def HasPrincipalSymbol (m : ℕ)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F)
    (σ : ∀ x : M, (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) →
      (E x →ₗ[ℂ] F x)) : Prop :=
  ∀ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
          (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e],
        ∀ (f : Trivialization (EuclideanSpace ℂ (Fin q))
            (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f],
          ∀ (U : Set M), IsOpen U →
            ∀ Q : CoordinateDifferentialOperator n r q m (c '' U),
              HasCoordinateExpression E F m P c e f U Q →
                ∀ x ∈ U, ∀ ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ,
                  (f.linearMapAt ℂ x).comp (σ x ξ) =
                    (Q.principalSymbol (c x) (covectorInChart c x ξ)).toLinearMap.comp
                      (e.linearMapAt ℂ x)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace DifferentialOperator

variable {E F} {m : ℕ}


set_option linter.unusedSectionVars false in
/-- A differential operator depends only on the germ of its input section. -/
theorem apply_eq_of_eventually_eq
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (s t : smoothSections (n := n) (r := r) E) (x : M)
    (h : ∀ᶠ y in 𝓝 x, s.val y = t.val y) :
    (P.toLinearMap s).val x = (P.toLinearMap t).val x := by
  /- Choose manifold and bundle charts at x and a local finite expression for P.
  Shrink its open domain to where s and t agree. Their coordinate expressions have
  equal derivatives of every order at the coordinate of x, so the two finite sums
  agree. The output bundle chart is injective on the fiber, giving the assertion. -/
  classical
  -- Choose one actual coordinate expression at the original point.
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have hx : x ∈ c.source := mem_chart_source _ x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
  obtain ⟨U, _, hxU, Q, hQ⟩ :=
    P.isDifferentialOperator c (chart_mem_atlas _ x) e f x ⟨⟨hx, he⟩, hf⟩
  -- Pull the common input germ into this chart before comparing its derivatives.
  have hcoord : sectionInChart E c e s.val =ᶠ[𝓝 (c x)]
      sectionInChart E c e t.val := by
    filter_upwards [(c.tendsto_symm hx).eventually h] with z hz
    dsimp only [sectionInChart]
    rw [hz]
  have hlocal : Q.apply (sectionInChart E c e s.val) (c x) =
      Q.apply (sectionInChart E c e t.val) (c x) := by
    simp only [CoordinateDifferentialOperator.apply]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro α _
    rw [(hcoord.iteratedFDeriv ℝ k.val).eq_of_nhds]
  -- Recover equality in the same original output fiber, using its inverse chart.
  have houtput := (hQ.2 s x hxU).trans (hlocal.trans (hQ.2 t x hxU).symm)
  calc
    (P.toLinearMap s).val x =
        f.symm x (f ⟨x, (P.toLinearMap s).val x⟩).2 :=
      (f.symm_apply_apply_mk hf _).symm
    _ = f.symm x (f ⟨x, (P.toLinearMap t).val x⟩).2 := congrArg (f.symm x) houtput
    _ = (P.toLinearMap t).val x := f.symm_apply_apply_mk hf _


set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The highest-order polynomials glue to a unique global principal symbol. -/
theorem existsUnique_principalSymbol (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) :
    ∃! σ : ∀ x : M, (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) → (E x →ₗ[ℂ] F x),
      HasPrincipalSymbol E F m P.toLinearMap σ := by
  /- Evaluate a vanishing scalar power times a section using the Faà di Bruno
  and product rules: only its top jet contributes. Smooth cutoffs realize any
  covector and input fiber vector by global test sections. Evaluating the same
  test in each coordinate expression compares their transported leading
  polynomials. A reference expression at each point defines the symbol;
  the comparison supplies all chart identities and forces uniqueness. -/
  classical
  -- Stage 1: the Faà di Bruno expansion identifies the jets of a vanishing scalar power.
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
  -- Stage 4: smooth cutoffs realize the same covector and input vector globally.
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
  have exists_section_value (x : M) (v : E x) :
      ∃ s : AtiyahSinger.smoothSections (n := n) (r := r) E, s.val x = v := by
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
    refine ⟨⟨s, hs⟩, ?_⟩
    dsimp only [s]
    rw [b.eq_one, Complex.ofReal_one, one_smul, e.symmL_apply hx]
    exact e.symm_apply_apply_mk hx v
  -- Stage 5: compare every chart expression on that single global test section.
  have exists_power_section (φ : M → ℝ)
      (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ)
      (s : smoothSections (n := n) (r := r) E) :
      ∃ t : smoothSections (n := n) (r := r) E,
        ∀ y, t.val y = ((φ y) ^ m : ℂ) • s.val y := by
    refine ⟨⟨fun y ↦ ((φ y) ^ m : ℂ) • s.val y, ?_⟩, fun _ ↦ rfl⟩
    intro e he
    let := he
    have hpower : ContDiff ℝ ∞ (fun t : ℝ ↦ (t ^ m : ℂ)) :=
      Complex.ofRealCLM.contDiff.pow m
    have hscalar := hpower.comp_contMDiff hφ
    have hmul : ContDiff ℝ ∞
        (fun p : ℂ × EuclideanSpace ℂ (Fin r) ↦ p.1 • p.2) := contDiff_smul
    have hcoords := hmul.contMDiff.comp_contMDiffOn
      (hscalar.contMDiffOn.prodMk_space (s.property e he))
    apply hcoords.congr
    intro y hy
    exact (e.linearEquivAt ℂ y hy).map_smul ((φ y) ^ m : ℂ) (s.val y)
  have test_evaluation
      (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
      (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
      (φ : M → ℝ) (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ)
      (hφx : φ x = 0) (hφd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x = ξ)
      (s t : smoothSections (n := n) (r := r) E)
      (ht : ∀ y, t.val y = ((φ y) ^ m : ℂ) • s.val y)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e]
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f]
      (U : Set M) (Q : CoordinateDifferentialOperator n r q m (c '' U))
      (hQ : HasCoordinateExpression E F m P.toLinearMap c e f U Q) (hxU : x ∈ U) :
      f.linearMapAt ℂ x ((P.toLinearMap t).val x) =
        ((-Complex.I) ^ m * (m.factorial : ℂ)) •
          Q.principalSymbol (c x) (covectorInChart c x ξ) (e.linearMapAt ℂ x (s.val x)) := by
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
        (fun z ↦ (ψ z) ^ m • g z) := by
      filter_upwards [(c.tendsto_symm hx.1.1).eventually
        (e.open_baseSet.mem_nhds hx.1.2)] with z hz
      dsimp only [sectionInChart, ψ, g, Function.comp_apply]
      rw [ht]
      change (e.linearEquivAt ℂ (c.symm z) hz) (((φ (c.symm z)) ^ m : ℂ) •
        s.val (c.symm z)) = _
      rw [map_smul, ← Complex.ofReal_pow, Complex.coe_smul]
      rfl
    have happly : Q.apply (sectionInChart E c e t.val) (c x) =
        Q.apply (fun z ↦ (ψ z) ^ m • g z) (c x) := by
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
  -- Stage 6: a reference expression defines the symbol; all expressions and uniqueness follow.
  classical
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have he (x : M) : x ∈ (e x).baseSet := mem_baseSet_trivializationAt _ _ x
  have hf (x : M) : x ∈ (f x).baseSet := mem_baseSet_trivializationAt _ _ x
  have hlocal (x : M) := P.isDifferentialOperator (c x) (chart_mem_atlas _ x)
    (e x) (f x) x ⟨⟨mem_chart_source _ x, he x⟩, hf x⟩
  choose U hU hxU Q hQ using hlocal
  let σ (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      E x →ₗ[ℂ] F x :=
    ((f x).linearEquivAt ℂ x (hf x)).symm.toLinearMap.comp
      (((Q x).principalSymbol (c x x) (covectorInChart (c x) x ξ)).toLinearMap.comp
        ((e x).linearMapAt ℂ x))
  let C : ℂ := (-Complex.I) ^ m * (m.factorial : ℂ)
  have hC : C ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
      (by exact_mod_cast Nat.factorial_ne_zero m)
  have hσ : HasPrincipalSymbol E F m P.toLinearMap σ := by
    intro c' hc' e' he' f' hf' V _ R hR x hx ξ
    apply LinearMap.ext
    intro v
    -- A common smooth section with zero lower jets compares the actual two expressions.
    obtain ⟨φ, hφ, hφx, hφd⟩ := exists_scalar_jet x ξ
    obtain ⟨s, hs⟩ := exists_section_value x v
    obtain ⟨t, ht⟩ := exists_power_section φ hφ s
    have htest0 := test_evaluation P x ξ φ hφ hφx hφd s t ht
      (c x) (chart_mem_atlas _ x) (e x) (f x) (U x) (Q x) (hQ x) (hxU x)
    have htest : (P.toLinearMap t).val x = C • σ x ξ v := by
      apply ((f x).linearEquivAt ℂ x (hf x)).injective
      simpa [σ, C, LinearMap.comp_apply, (f x).linearMapAt_def_of_mem (hf x),
        (f x).apply_mk_symm (hf x), hs] using htest0
    have htest1 := test_evaluation P x ξ φ hφ hφx hφd s t ht c' hc' e' f' V R hR hx
    rw [htest, map_smul, hs] at htest1
    exact smul_right_injective _ hC htest1
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  funext x ξ
  apply LinearMap.ext
  intro v
  have hτx := LinearMap.congr_fun
    (hτ (c x) (chart_mem_atlas _ x) (e x) (f x) (U x) (hU x) (Q x) (hQ x) x (hxU x) ξ) v
  have hσx := LinearMap.congr_fun
    (hσ (c x) (chart_mem_atlas _ x) (e x) (f x) (U x) (hU x) (Q x) (hQ x) x (hxU x) ξ) v
  apply ((f x).linearEquivAt ℂ x (hf x)).injective
  simpa [LinearMap.comp_apply, (f x).linearMapAt_def_of_mem (hf x)]
    using hτx.trans hσx.symm

/-- The principal symbol selected by its unique local specification. -/
def principalSymbol (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) :
    ∀ x : M, (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) → (E x →ₗ[ℂ] F x) :=
  Classical.choose P.existsUnique_principalSymbol.exists

/-- The selected symbol satisfies every compatible coordinate expression. -/
theorem hasPrincipalSymbol (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) :
    HasPrincipalSymbol E F m P.toLinearMap P.principalSymbol := by
  /- Apply the specification of the chosen witness in existsUnique_principalSymbol.
  It quantifies over all atlas charts, linear bundle charts and representing expressions,
  so this identifies the symbol independently of any local choices used in constructing it. -/
  exact Classical.choose_spec P.existsUnique_principalSymbol.exists

set_option backward.isDefEq.respectTransparency false in
/-- The real-scalar Leibniz law of a first-order operator identifies its principal symbol.
This is the standard commutator characterization in the convention `D_j = -i ∂_j`.
It applies to the full Dirac operator and to both of its actual chiral compressions. -/
theorem principalSymbol_eq_smul_of_leibniz
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F 1)
    (a : ∀ x : M, (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) →
      (E x →ₗ[ℂ] F x))
    (h : ∀ (φ : M → ℝ)
      (_hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ)
      (s t : smoothSections (n := n) (r := r) E),
      (∀ y, t.val y = (φ y : ℂ) • s.val y) → ∀ x,
      (P.toLinearMap t).val x =
        a x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x) (s.val x) +
          (φ x : ℂ) • (P.toLinearMap s).val x)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    P.principalSymbol x ξ = Complex.I • a x ξ := by
  /- First evaluate a vanishing scalar times a section in an actual coordinate
  expression. Smooth bumps realize any original covector and fiber vector. Comparing
  this test with the supplied Leibniz law recovers the same native principal symbol. -/
  classical
  -- Stage 1: the first-order product rule isolates the principal coefficient.
  have coordinate_apply_one {U : Set (EuclideanSpace ℝ (Fin n))}
      (Q : CoordinateDifferentialOperator n r q 1 U)
      (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
      (x : EuclideanSpace ℝ (Fin n))
      (hφ : DifferentiableAt ℝ φ x) (hg : DifferentiableAt ℝ g x) (hφx : φ x = 0) :
      Q.apply (fun z ↦ φ z • g z) x =
        -Complex.I • Q.principalSymbol x
          (WithLp.toLp 2 fun j ↦ fderiv ℝ φ x (EuclideanSpace.single j 1)) (g x) := by
    -- Only first derivatives of the vanishing scalar remain in the order-one expression.
    have hd : fderiv ℝ (fun z ↦ φ z • g z) x =
        (fderiv ℝ φ x).smulRight (g x) := by
      change fderiv ℝ (φ • g) x = _
      rw [fderiv_smul hφ hg, hφx, zero_smul, zero_add]
    unfold CoordinateDifferentialOperator.apply CoordinateDifferentialOperator.principalSymbol
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, one_smul,
      iteratedFDeriv_zero_apply, hφx, zero_smul, map_zero, Finset.sum_const_zero, zero_add,
      pow_one, iteratedFDeriv_one_apply, hd, ContinuousLinearMap.smulRight_apply,
      Fin.prod_univ_one, sum_apply, smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [map_smul, ContinuousLinearMap.map_smul_of_tower]
    rfl
  -- Stage 2: realize arbitrary original first jets and section values globally.
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
  have exists_section_value (x : M) (v : E x) :
      ∃ s : AtiyahSinger.smoothSections (n := n) (r := r) E, s.val x = v := by
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
    refine ⟨⟨s, hs⟩, ?_⟩
    dsimp only [s]
    rw [b.eq_one, Complex.ofReal_one, one_smul, e.symmL_apply hx]
    exact e.symm_apply_apply_mk hx v
  -- Stage 3: transport the same scalar-times-section test into a differential chart.
  have exists_scalar_section (φ : M → ℝ)
      (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ)
      (s : smoothSections (n := n) (r := r) E) :
      ∃ t : smoothSections (n := n) (r := r) E,
        ∀ y, t.val y = (φ y : ℂ) • s.val y := by
    refine ⟨⟨fun y ↦ (φ y : ℂ) • s.val y, ?_⟩, fun _ ↦ rfl⟩
    intro e he
    let := he
    have hscalar := Complex.ofRealCLM.contMDiff.comp hφ
    have hmul : ContDiff ℝ ∞
        (fun p : ℂ × EuclideanSpace ℂ (Fin r) ↦ p.1 • p.2) := contDiff_smul
    have hcoords := hmul.contMDiff.comp_contMDiffOn
      (hscalar.contMDiffOn.prodMk_space (s.property e he))
    apply hcoords.congr
    intro y hy
    exact (e.linearEquivAt ℂ y hy).map_smul (φ y : ℂ) (s.val y)
  have test_evaluation
      (P : DifferentialOperator (n := n) (r := r) (q := q) E F 1)
      (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
      (φ : M → ℝ) (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ)
      (hφx : φ x = 0) (hφd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x = ξ)
      (s t : smoothSections (n := n) (r := r) E)
      (ht : ∀ y, t.val y = (φ y : ℂ) • s.val y)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e]
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f]
      (U : Set M) (Q : CoordinateDifferentialOperator n r q 1 (c '' U))
      (hQ : HasCoordinateExpression E F 1 P.toLinearMap c e f U Q) (hxU : x ∈ U) :
      f.linearMapAt ℂ x ((P.toLinearMap t).val x) =
        -Complex.I •
          Q.principalSymbol (c x) (covectorInChart c x ξ) (e.linearMapAt ℂ x (s.val x)) := by
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
        (fun z ↦ ψ z • g z) := by
      filter_upwards [(c.tendsto_symm hx.1.1).eventually
        (e.open_baseSet.mem_nhds hx.1.2)] with z hz
      dsimp only [sectionInChart, ψ, g, Function.comp_apply]
      rw [ht]
      change (e.linearEquivAt ℂ (c.symm z) hz) ((φ (c.symm z) : ℂ) •
        s.val (c.symm z)) = _
      rw [map_smul, Complex.coe_smul]
      rfl
    have happly : Q.apply (sectionInChart E c e t.val) (c x) =
        Q.apply (fun z ↦ ψ z • g z) (c x) := by
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
      coordinate_apply_one Q ψ g (c x) (hψ.differentiableAt (by simp))
        (hg.differentiableAt (by simp)) hψx, hcov]
    congr 1
    dsimp only [g, sectionInChart]
    rw [c.left_inv hx.1.1, e.coe_linearMapAt_of_mem hx.1.2]
  -- Stage 4: compare with the supplied Leibniz law and the existing symbol specification.
  apply LinearMap.ext
  intro v
  obtain ⟨φ, hφ, hφx, hφd⟩ := exists_scalar_jet x ξ
  obtain ⟨s, hs⟩ := exists_section_value x v
  obtain ⟨t, ht⟩ := exists_scalar_section φ hφ s
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
  obtain ⟨U, hU, hxU, Q, hQ⟩ := P.isDifferentialOperator c (chart_mem_atlas _ x)
    e f x ⟨⟨mem_chart_source _ x, he⟩, hf⟩
  have htest := test_evaluation P x ξ φ hφ hφx hφd s t ht
    c (chart_mem_atlas _ x) e f U Q hQ hxU
  have hleib := h φ hφ s t ht x
  rw [hφd, hφx, Complex.ofReal_zero, zero_smul, add_zero, hs] at hleib
  have hsymbol := LinearMap.congr_fun
    (P.hasPrincipalSymbol c (chart_mem_atlas _ x) e f U hU Q hQ x hxU ξ) v
  change f.linearMapAt ℂ x (P.principalSymbol x ξ v) =
    Q.principalSymbol (c x) (covectorInChart c x ξ) (e.linearMapAt ℂ x v) at hsymbol
  rw [hleib, hs] at htest
  rw [← hsymbol] at htest
  -- Multiplication by +i cancels the coordinate convention -i, in the same output fiber.
  have hcoord := congrArg (fun w ↦ Complex.I • w) htest
  simp only [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul] at hcoord
  apply (f.linearEquivAt ℂ x hf).injective
  simpa only [Trivialization.linearEquivAt_apply, f.coe_linearMapAt_of_mem hf,
    LinearMap.smul_apply, map_smul] using hcoord.symm

/-- The principal symbol is homogeneous of degree m, for all real scaling factors. -/
theorem principalSymbol_smul (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) (t : ℝ) :
    P.principalSymbol x (t • ξ) = (t : ℂ) ^ m • P.principalSymbol x ξ := by
  /- In any local expression, each leading term contains exactly m covector factors.
  Pullback of covectors is linear, so scaling multiplies each term by t^m. Transport
  through the linear fiber charts. This polynomial identity includes t=0 and m=0. -/
  classical
  -- Use the same actual local expression for both covectors.
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
  obtain ⟨U, hU, hxU, Q, hQ⟩ :=
    P.isDifferentialOperator c (chart_mem_atlas _ x) e f x
      ⟨⟨mem_chart_source _ x, he⟩, hf⟩
  have hscale : covectorInChart c x (t • ξ) = t • covectorInChart c x ξ := by
    ext j
    rfl
  have hpoly : Q.principalSymbol (c x) (t • covectorInChart c x ξ) =
      (t : ℂ) ^ m • Q.principalSymbol (c x) (covectorInChart c x ξ) := by
    -- Every ordered monomial has exactly m factors, also at zero or negative t.
    simp only [CoordinateDifferentialOperator.principalSymbol, PiLp.smul_apply,
      smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.smul_sum, ← Complex.coe_smul, smul_smul,
      Complex.ofReal_mul, Complex.ofReal_pow]
  apply LinearMap.ext
  intro v
  have h₁ := LinearMap.congr_fun
    (P.hasPrincipalSymbol c (chart_mem_atlas _ x) e f U hU Q hQ x hxU (t • ξ)) v
  have h₂ := LinearMap.congr_fun
    (P.hasPrincipalSymbol c (chart_mem_atlas _ x) e f U hU Q hQ x hxU ξ) v
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at h₁ h₂
  rw [hscale, hpoly, smul_apply] at h₁
  have hout := h₁.trans (congrArg (fun w ↦ (t : ℂ) ^ m • w) h₂.symm)
  apply (f.linearEquivAt ℂ x hf).injective
  simpa [f.linearMapAt_def_of_mem hf] using hout

/-- The symbol is jointly smooth in base and cotangent coordinates.
The input fiber vector is fixed in a local frame; varying it over a basis gives all entries. -/
theorem contDiffOn_principalSymbol_in_chart
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e]
    (f : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f]
    (v : EuclideanSpace ℂ (Fin r)) :
    ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        f.linearMapAt ℂ (c.symm z.1)
          (P.principalSymbol (c.symm z.1)
            ((innerSL ℝ z.2).comp
              (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c (c.symm z.1)))
            (e.symmL ℂ (c.symm z.1) v)))
      ((c.target ∩ c.symm ⁻¹' e.baseSet ∩ c.symm ⁻¹' f.baseSet) ×ˢ Set.univ) := by
  /- The coordinate covector η is pulled back by the derivative of c, giving the
  covector at c⁻¹(z). The inverse function identity shows covectorInChart recovers η.
  In any local expression the displayed map is therefore a finite sum of smooth
  coefficients times degree-m monomials in η, applied to v. These local descriptions
  cover the chart overlap. Smoothness is local, so it holds on the displayed open set. -/
  classical
  have hσ := P.hasPrincipalSymbol
  intro z hz
  -- Work with one actual local expression around the original base point.
  have hx : c.symm z.1 ∈ c.source ∩ e.baseSet ∩ f.baseSet :=
    ⟨⟨c.map_target hz.1.1.1, hz.1.1.2⟩, hz.1.2⟩
  obtain ⟨U, hU, hxU, Q, hQ⟩ := P.isDifferentialOperator c hc e f (c.symm z.1) hx
  have hUs : U ⊆ c.source := fun y hy ↦ (hQ.1 hy).1.1
  have hV : IsOpen (c '' U) := c.isOpen_image_of_subset_source hU hUs
  have hzV : z.1 ∈ c '' U := ⟨c.symm z.1, hxU, c.right_inv hz.1.1.1⟩
  -- The original top polynomial has smooth coefficients and finite frequency monomials.
  have htop : ContDiffOn ℝ ∞ (Function.uncurry Q.principalSymbol)
      ((c '' U) ×ˢ Set.univ) := by
    unfold CoordinateDifferentialOperator.principalSymbol Function.uncurry
    apply ContDiffOn.sum
    intro α _
    have hmonomial : ContDiff ℝ ∞
        (fun w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          ∏ j : Fin m, w.2 (α j)) := by
      exact contDiff_prod fun j _ ↦
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) (α j)).contDiff.comp contDiff_snd
    exact hmonomial.contDiffOn.smul
      ((Q.smooth_coefficient ⟨m, Nat.lt_succ_self m⟩ α).comp contDiffOn_fst
        (fun w hw ↦ hw.1))
  have htopAt : ContDiffAt ℝ ∞
      (fun w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        Q.principalSymbol w.1 w.2 v) z :=
    (htop.contDiffAt ((hV.prod isOpen_univ).mem_nhds
      ⟨hzV, Set.mem_univ z.2⟩)).continuousLinearMap_comp
        ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin q)) v).restrictScalars ℝ)
  apply ContDiffAt.contDiffWithinAt
  apply htopAt.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt (hV.mem_nhds hzV)] with w hw
  obtain ⟨y, hy, hcy⟩ := hw
  have hyc := hUs hy
  have hbase : c.symm w.1 = y := by rw [← hcy, c.left_inv hyc]
  change f.linearMapAt ℂ (c.symm w.1)
    (P.principalSymbol (c.symm w.1) _ (e.symmL ℂ (c.symm w.1) v)) = Q.principalSymbol w.1 w.2 v
  rw [hbase]
  -- On this chart domain the two differential maps cancel before reading the covector.
  have hcov : covectorInChart c y ((innerSL ℝ w.2).comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c y)) = w.2 := by
    have hderiv := (mdifferentiable_of_mem_atlas
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hc).comp_symm_deriv (c.map_source hyc)
    rw [c.left_inv hyc] at hderiv
    ext j
    change inner ℝ w.2 ((mfderiv _ _ c y)
      ((mfderiv _ _ c.symm (c y)) (EuclideanSpace.single j 1))) = w.2 j
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) ↦ L (EuclideanSpace.single j 1)) hderiv
    change (mfderiv _ _ c y) ((mfderiv _ _ c.symm (c y))
      (EuclideanSpace.single j 1)) = EuclideanSpace.single j 1 at h
    rw [h]
    simp [EuclideanSpace.inner_single_right]
  -- Evaluate the specified map equality on the same inverse-frame vector.
  have hspec := congrArg (fun L : E y →ₗ[ℂ] EuclideanSpace ℂ (Fin q) ↦
      L (e.symmL ℂ y v))
    (hσ c hc e f U hU Q hQ y hy ((innerSL ℝ w.2).comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c y)))
  simp only [LinearMap.comp_apply, hcov, e.symmL_apply (hQ.1 hy).1.2,
    e.linearMapAt_symm (hQ.1 hy).1.2, hcy] at hspec
  simpa only [e.symmL_apply (hQ.1 hy).1.2, ContinuousLinearMap.coe_coe] using hspec

/-- Ellipticity means that the principal symbol is an isomorphism off the zero section. -/
def IsElliptic (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) : Prop :=
  ∀ (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ), ξ ≠ 0 →
    Function.Bijective (P.principalSymbol x ξ)

/-- The analytic index of this elliptic operator, computed from its actual smooth section map. -/
def analyticIndex [CompactSpace M]
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (_hP : P.IsElliptic) : ℤ :=
  P.toLinearMap.index

/-- The analytic index is the smooth kernel finrank minus the smooth cokernel finrank. -/
theorem analyticIndex_eq_finrank_sub [CompactSpace M]
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) (hP : P.IsElliptic) :
    P.analyticIndex hP = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) := by
  /- Unfold the analytic index and use the algebraic index formula. Finiteness
  of the smooth kernel and cokernel is a separate elliptic result; this equality
  alone neither establishes it nor identifies a Hilbert adjoint with the formal
  adjoint. -/

  exact LinearMap.index_eq_finrank_sub

end DifferentialOperator

end AtiyahSinger
