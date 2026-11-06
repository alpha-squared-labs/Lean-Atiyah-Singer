/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HodgeDecomposition

/-!
# The actual even-to-odd Hodge--de Rham operator

Public module ID: M0700.

E06: the even and odd form spaces are the parity subspaces of the existing
total direct sum of smooth differential forms. The positive Hodge--de Rham
operator is the restriction of the same d plus metric codifferential from
even forms to odd forms. Its cokernel is the algebraic quotient by its actual
smooth range, with no closure or Hilbert completion substituted.

On a compact manifold the even harmonic forms identify with that actual
kernel by inclusion, while odd harmonic forms identify with the actual
cokernel by the original quotient map. These canonical maps retain the
representatives needed for the later equivariant comparison. Finiteness is
stated for the actual kernel and quotient carriers.

Sources: Lawson--Michelsohn, Spin Geometry, II.5.12--5.15 and the orientability
note, pp.123--126; III.5.5--5.6, p.195; III.9.3, pp.211--212, for the kernel
minus cokernel definition of index; and III.13.7, p.253, for its use on the
graded de Rham sphere operator. The complex coefficient extension retains
the existing HODGE-COMPLEXIFICATION-SOURCE supplement. The standard graded
kernel/cokernel description below expands these Hodge statements; it does
not claim a separately numbered lemma absent from the book.

The full Euclidean model excludes a boundary. No orientation, connectedness,
positive dimension or nonempty base is assumed. All nonnegative degrees are
retained in the total direct sum; degrees above the dimension vanish as actual
alternating forms, rather than being truncated by an unrelated carrier.
The operators exist without compactness; the global Hodge identifications
and finite-dimensionality require compactness.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped DirectSum Manifold ContDiff

set_option maxSynthPendingDepth 25

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Even smooth forms are exactly total forms whose odd-degree components vanish. -/
def evenSmoothDifferentialForms : Submodule ℂ (TotalSmoothDifferentialForm (n := n) M) where
  carrier := {form | ∀ p : ℕ, Odd p → form p = 0}
  zero_mem' := by
    intro p hp
    rfl
  add_mem' := by
    intro form other hform hother p hp
    change form p + other p = 0
    rw [hform p hp, hother p hp, add_zero]
  smul_mem' := by
    intro a form hform p hp
    change a • form p = 0
    rw [hform p hp, smul_zero]

/-- Odd smooth forms are exactly total forms whose even-degree components vanish. -/
def oddSmoothDifferentialForms : Submodule ℂ (TotalSmoothDifferentialForm (n := n) M) where
  carrier := {form | ∀ p : ℕ, Even p → form p = 0}
  zero_mem' := by
    intro p hp
    rfl
  add_mem' := by
    intro form other hform hother p hp
    change form p + other p = 0
    rw [hform p hp, hother p hp, add_zero]
  smul_mem' := by
    intro a form hform p hp
    change a • form p = 0
    rw [hform p hp, smul_zero]

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  (g : SmoothTangentMetric (n := n) (M := M))

/-- The actual Hodge--de Rham operator interchanges the even and odd form spaces. -/
theorem totalFormHodgeDirac_maps_parity :
    (∀ form : evenSmoothDifferentialForms (n := n) (M := M),
      totalFormHodgeDirac g form.val ∈ oddSmoothDifferentialForms (n := n) (M := M)) ∧
    (∀ form : oddSmoothDifferentialForms (n := n) (M := M),
      totalFormHodgeDirac g form.val ∈ evenSmoothDifferentialForms (n := n) (M := M)) := by
  /- Stage 1: evaluate the direct-sum construction on each homogeneous
  summand. The original exterior derivative raises its degree by one, and
  the original codifferential lowers every positive degree by one. Both
  operations reverse parity. Stage 2: the codifferential is zero in degree
  zero, so there is no negative-degree term. Extend across each form's finite
  degree support. This is an actual grading identity, with no compactness
  or top-degree truncation hypothesis. -/
  classical
  -- A homogeneous input can contribute only in the two adjacent degrees.
  have hparity (form : TotalSmoothDifferentialForm (n := n) M) (b : ℕ)
      (hform : ∀ p : ℕ, p % 2 ≠ b → form p = 0) :
      ∀ q : ℕ, q % 2 = b → (totalFormHodgeDirac g form) q = 0 := by
    intro q hq
    rw [← DirectSum.sum_support_of form, map_sum, DFinsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro p _
    change (totalFormHodgeDirac g
      (DirectSum.lof ℂ ℕ (SmoothDifferentialForm (n := n) M) p (form p))) q = 0
    by_cases hp : p % 2 = b
    · have hraise : q ≠ p + 1 := by omega
      cases p with
      | zero =>
          simp only [totalFormHodgeDirac, LinearMap.add_apply, totalFormExteriorDerivative,
            totalFormCodifferential, DirectSum.toModule_lof, LinearMap.comp_apply]
          simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hraise]
      | succ p =>
          have hlower : q ≠ p := by omega
          simp only [totalFormHodgeDirac, LinearMap.add_apply, totalFormExteriorDerivative,
            totalFormCodifferential, DirectSum.toModule_lof, LinearMap.comp_apply]
          simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hraise, hlower]
    · rw [hform p hp, map_zero, map_zero]
      rfl
  -- Reconstruct each finite total form without truncating any homogeneous degree.
  constructor
  · intro form
    change ∀ q : ℕ, Even q → (totalFormHodgeDirac g form.val) q = 0
    intro q hq
    apply hparity form.val 0 _ q (Nat.even_iff.mp hq)
    intro p hp
    exact form.property p (Nat.odd_iff.mpr (by omega))
  · intro form
    change ∀ q : ℕ, Odd q → (totalFormHodgeDirac g form.val) q = 0
    intro q hq
    apply hparity form.val 1 _ q (Nat.odd_iff.mp hq)
    intro p hp
    exact form.property p (Nat.even_iff.mpr (by omega))

/-- The positive Hodge--de Rham operator is the actual d plus delta from even to odd forms. -/
def positiveHodgeDirac :
    evenSmoothDifferentialForms (n := n) (M := M) →ₗ[ℂ]
      oddSmoothDifferentialForms (n := n) (M := M) :=
  (totalFormHodgeDirac g).restrict (by
    intro form hform
    exact (totalFormHodgeDirac_maps_parity g).1 ⟨form, hform⟩)

/-- The negative Hodge--de Rham operator is the same d plus delta from odd to even forms. -/
def negativeHodgeDirac :
    oddSmoothDifferentialForms (n := n) (M := M) →ₗ[ℂ]
      evenSmoothDifferentialForms (n := n) (M := M) :=
  (totalFormHodgeDirac g).restrict (by
    intro form hform
    exact (totalFormHodgeDirac_maps_parity g).2 ⟨form, hform⟩)

/-- Even harmonic forms are the original total Laplacian kernel within the even forms. -/
def evenHarmonicForms : Submodule ℂ (evenSmoothDifferentialForms (n := n) (M := M)) :=
  (LinearMap.ker (totalFormHodgeLaplacian g)).comap
    (evenSmoothDifferentialForms (n := n) (M := M)).subtype

/-- Odd harmonic forms are the original total Laplacian kernel within the odd forms. -/
def oddHarmonicForms : Submodule ℂ (oddSmoothDifferentialForms (n := n) (M := M)) :=
  (LinearMap.ker (totalFormHodgeLaplacian g)).comap
    (oddSmoothDifferentialForms (n := n) (M := M)).subtype

set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the harmonic-space and smooth quotient-cokernel comparison.
/-- The actual algebraic cokernel of the positive Hodge--de Rham operator on smooth forms. -/
abbrev PositiveHodgeCokernel : Type _ :=
  (↥(oddSmoothDifferentialForms (n := n) (M := M)) : Type _) ⧸
    (positiveHodgeDirac g).range

/-- The canonical even harmonic-to-kernel map keeps the same original smooth form. -/
def evenHarmonicToPositiveKernel [CompactSpace M] :
    evenHarmonicForms g →ₗ[ℂ] LinearMap.ker (positiveHodgeDirac g) where
  toFun form := ⟨form.val, by
    apply Subtype.ext
    have hmem : form.val.val ∈ LinearMap.ker (totalFormHodgeLaplacian g) := form.property
    rw [← totalFormHodgeDirac_ker_eq g] at hmem
    exact hmem⟩
  map_add' := by
    intro form other
    rfl
  map_smul' := by
    intro a form
    rfl

/-- The canonical odd harmonic-to-cokernel map is the original range quotient on that form. -/
def oddHarmonicToPositiveCokernel : oddHarmonicForms g →ₗ[ℂ] PositiveHodgeCokernel g :=
  (positiveHodgeDirac g).range.mkQ.comp (oddHarmonicForms g).subtype

/-- Even harmonic forms map bijectively onto the actual positive Hodge--de Rham kernel. -/
theorem evenHarmonicToPositiveKernel_bijective [CompactSpace M] :
    Function.Bijective (evenHarmonicToPositiveKernel g) := by
  /- The forward map preserves the original form, hence is injective.
  Conversely an actual positive-operator kernel vector has zero total
  Hodge--de Rham image, since the target odd-form subtype has the same
  underlying total form. The total square identity makes its Laplacian
  vanish. Thus it belongs to the even harmonic subspace, and the canonical
  map sends this same form back to the original kernel element. -/
  constructor
  · -- The canonical map retains the same smooth total form in its subtypes.
    intro form other h
    apply Subtype.ext
    exact congrArg (fun u : LinearMap.ker (positiveHodgeDirac g) ↦ u.val) h
  · -- The square identity sends this actual Dirac kernel element to the Laplacian kernel.
    intro form
    have hdirac : totalFormHodgeDirac g form.val.val = 0 := by
      exact congrArg Subtype.val form.property
    have hlaplacian : totalFormHodgeLaplacian g form.val.val = 0 := by
      rw [← totalFormHodgeDirac_comp, LinearMap.comp_apply, hdirac, map_zero]
    refine ⟨⟨form.val, hlaplacian⟩, ?_⟩
    rfl

set_option maxHeartbeats 1500000 in
-- The extended limit accommodates the harmonic-space and smooth quotient-cokernel comparison.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the harmonic-space and smooth quotient-cokernel comparison.
/-- Odd harmonic forms map bijectively onto the actual positive smooth quotient-cokernel. -/
theorem oddHarmonicToPositiveCokernel_bijective [CompactSpace M] :
    Function.Bijective (oddHarmonicToPositiveCokernel g) := by
  /- For injectivity, the existing identity ker D = ker D² shows that an
  actual Dirac image lying in ker D is zero. For surjectivity, decompose
  each occupied odd degree as a harmonic component plus a Laplacian image.
  The finite sum stays odd, and its Laplacian image is D applied to the
  even form obtained by applying D once. All representatives and the
  quotient by the actual smooth range remain unchanged. -/
  classical
  let F := SmoothDifferentialForm (n := n) M
  let L (p : ℕ) := DirectSum.lof ℂ ℕ F p
  let D := totalFormHodgeDirac g
  let Δ := totalFormHodgeLaplacian g
  have hker (v : TotalSmoothDifferentialForm (n := n) M) (hv : Δ v = 0) :
      D v = 0 := by
    change v ∈ LinearMap.ker (totalFormHodgeDirac g)
    rw [totalFormHodgeDirac_ker_eq]
    exact hv
  constructor
  · -- ker D = ker D² implies that a harmonic vector in the actual range is zero.
    have hzero (u : oddHarmonicForms g) (hu : oddHarmonicToPositiveCokernel g u = 0) :
        u = 0 := by
      have hrange : u.val ∈ (positiveHodgeDirac g).range :=
        (Submodule.Quotient.mk_eq_zero _).mp hu
      obtain ⟨v, hv⟩ := hrange
      have hv' : D v.val = u.val.val := congrArg Subtype.val hv
      have hΔ : Δ v.val = 0 := by
        change totalFormHodgeLaplacian g v.val = 0
        rw [← totalFormHodgeDirac_comp, LinearMap.comp_apply]
        change D (D v.val) = 0
        rw [hv', hker u.val.val u.property]
      apply Subtype.ext
      apply Subtype.ext
      exact hv'.symm.trans (hker v.val hΔ)
    intro u v huv
    apply sub_eq_zero.mp
    apply hzero (u - v)
    rw [map_sub, huv, sub_self]
  · -- Decompose each occupied degree, retaining exactly the original finite support.
    intro q
    obtain ⟨v, rfl⟩ := (positiveHodgeDirac g).range.mkQ_surjective q
    choose h u hu using fun p ↦ exists_harmonic_add_hodgeLaplacian g p (v.val p)
    let hs : TotalSmoothDifferentialForm (n := n) M :=
      ∑ p ∈ v.val.support, L p (h p).val
    let us : TotalSmoothDifferentialForm (n := n) M :=
      ∑ p ∈ v.val.support, L p (u p)
    have hodd (p : ℕ) (hp : p ∈ v.val.support) : Odd p := by
      by_contra hn
      exact (DFinsupp.mem_support_iff.mp hp) (v.property p (Nat.not_odd_iff_even.mp hn))
    have hlo (p : ℕ) (hp : Odd p) (a : F p) :
        L p a ∈ oddSmoothDifferentialForms (n := n) (M := M) := by
      intro r hr
      have hrp : r ≠ p := by
        intro heq
        subst r
        exact (Nat.not_even_iff_odd.mpr hp) hr
      simp [L, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hrp]
    have hhodd : hs ∈ oddSmoothDifferentialForms (n := n) (M := M) := by
      apply Submodule.sum_mem
      intro p hp
      exact hlo p (hodd p hp) (h p).val
    have huodd : us ∈ oddSmoothDifferentialForms (n := n) (M := M) := by
      apply Submodule.sum_mem
      intro p hp
      exact hlo p (hodd p hp) (u p)
    have hΔL (p : ℕ) (a : F p) : Δ (L p a) = L p (smoothFormHodgeLaplacian g p a) := by
      simp [Δ, L, F, totalFormHodgeLaplacian]
    have hharmonic : Δ hs = 0 := by
      change Δ (∑ p ∈ v.val.support, L p (h p).val) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro p _
      rw [hΔL, show smoothFormHodgeLaplacian g p (h p).val = 0 from (h p).property,
        map_zero]
    have hsplit : v.val = hs + Δ us := by
      change v.val = (∑ p ∈ v.val.support, L p (h p).val) +
        Δ (∑ p ∈ v.val.support, L p (u p))
      rw [map_sum, ← Finset.sum_add_distrib]
      conv_lhs => rw [← DirectSum.sum_support_of v.val]
      apply Finset.sum_congr rfl
      intro p _
      rw [hΔL, ← map_add, ← hu p]
      rfl
    let htotal : oddHarmonicForms g := ⟨⟨hs, hhodd⟩, hharmonic⟩
    let w := negativeHodgeDirac g ⟨us, huodd⟩
    have hpositive : (positiveHodgeDirac g w).val = Δ us := by
      change D (D us) = Δ us
      exact LinearMap.congr_fun (totalFormHodgeDirac_comp g) us
    have hv : v = htotal.val + positiveHodgeDirac g w := by
      apply Subtype.ext
      exact hsplit.trans (congrArg (hs + ·) hpositive.symm)
    refine ⟨htotal, ?_⟩
    change (positiveHodgeDirac g).range.mkQ htotal.val =
      (positiveHodgeDirac g).range.mkQ v
    rw [hv, map_add]
    have hz : (positiveHodgeDirac g).range.mkQ (positiveHodgeDirac g w) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, rfl⟩
    rw [hz, add_zero]

/-- The canonical even harmonic identification with the positive operator's actual kernel. -/
def evenHarmonicKernelEquiv [CompactSpace M] :
    evenHarmonicForms g ≃ₗ[ℂ] LinearMap.ker (positiveHodgeDirac g) :=
  LinearEquiv.ofBijective (evenHarmonicToPositiveKernel g)
    (evenHarmonicToPositiveKernel_bijective g)

/-- The canonical odd harmonic identification with the positive operator's actual cokernel. -/
def oddHarmonicCokernelEquiv [CompactSpace M] :
    oddHarmonicForms g ≃ₗ[ℂ] PositiveHodgeCokernel g :=
  LinearEquiv.ofBijective (oddHarmonicToPositiveCokernel g)
    (oddHarmonicToPositiveCokernel_bijective g)

/-- The actual total harmonic kernel is finite dimensional, including all natural degrees.
This is shared by the canonical even kernel and odd quotient-cokernel identifications. -/
private theorem finiteDimensional_totalFormHodgeLaplacian_ker [CompactSpace M] :
    FiniteDimensional ℂ (LinearMap.ker (totalFormHodgeLaplacian g)) := by
  classical
  let F := SmoothDifferentialForm (n := n) M
  have hcomponent (u : LinearMap.ker (totalFormHodgeLaplacian g)) (p : ℕ) :
      smoothFormHodgeLaplacian g p (u.val p) = 0 := by
    let proj := DirectSum.component ℂ ℕ F p
    have hmap : proj.comp (totalFormHodgeLaplacian g) =
        (smoothFormHodgeLaplacian g p).comp proj := by
      apply DirectSum.linearMap_ext
      intro q
      apply LinearMap.ext
      intro v
      by_cases hqp : q = p
      · subst q
        simp [proj, F, totalFormHodgeLaplacian]
      · simp [proj, F, totalFormHodgeLaplacian, DirectSum.component.of, hqp]
    have h := LinearMap.congr_fun hmap u.val
    rw [LinearMap.comp_apply, u.property, map_zero] at h
    exact h.symm
  -- Alternating forms above the actual tangent dimension vanish pointwise.
  have hhigh (p : ℕ) (hp : n < p) (u : F p) : u = 0 := by
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext_alternating
    intro v hv
    have hcard := Fintype.card_le_of_injective v hv
    simp only [Fintype.card_fin] at hcard
    omega
  -- The original total kernel embeds into its first n + 1 harmonic components.
  let T : LinearMap.ker (totalFormHodgeLaplacian g) →ₗ[ℂ]
      (p : Fin (n + 1)) → harmonicForms g p.val := {
    toFun u p := ⟨u.val p.val, hcomponent u p.val⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have (p : Fin (n + 1)) : FiniteDimensional ℂ (harmonicForms g p.val) :=
    finiteDimensional_harmonicForms g p.val
  apply FiniteDimensional.of_injective
    (V₂ := (p : Fin (n + 1)) → harmonicForms g p.val) T
  intro u v huv
  apply Subtype.ext
  apply DFinsupp.ext
  intro p
  by_cases hp : p < n + 1
  · exact congrArg Subtype.val (congrFun huv ⟨p, hp⟩)
  · rw [hhigh p (by omega) (u.val p), hhigh p (by omega) (v.val p)]

set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the harmonic-space and smooth quotient-cokernel comparison.
/-- The actual smooth kernel of the positive Hodge--de Rham operator is finite dimensional. -/
theorem finiteDimensional_positiveHodgeDirac_ker [CompactSpace M] :
    FiniteDimensional ℂ (LinearMap.ker (positiveHodgeDirac g)) := by
  /- Stage 1: the canonical even harmonic identification retains every
  original kernel form. Its homogeneous components belong to the actual
  finite-dimensional harmonic spaces from Hodge theory. Stage 2: an
  alternating p-form on an n-dimensional tangent fiber is zero for p > n.
  Hence only the finitely many even degrees at most n remain. Their finite
  direct sum is finite dimensional, and so is this actual kernel. -/
  have := finiteDimensional_totalFormHodgeLaplacian_ker g
  have : FiniteDimensional ℂ (evenHarmonicForms g) := by
    let T : evenHarmonicForms g →ₗ[ℂ] LinearMap.ker (totalFormHodgeLaplacian g) := {
      toFun u := ⟨u.val.val, u.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    apply FiniteDimensional.of_injective T
    intro u v h
    have heq : u.val.val = v.val.val :=
      congrArg (fun w : LinearMap.ker (totalFormHodgeLaplacian g) ↦ w.val) h
    exact Subtype.ext (Subtype.ext heq)
  exact (evenHarmonicKernelEquiv g).finiteDimensional

set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the harmonic-space and smooth quotient-cokernel comparison.
/-- The actual smooth quotient-cokernel of the positive Hodge operator is finite dimensional. -/
theorem finiteDimensional_positiveHodgeDirac_coker [CompactSpace M] :
    FiniteDimensional ℂ (PositiveHodgeCokernel g) := by
  /- Use the canonical odd harmonic-to-quotient equivalence, whose forward
  map is the original range quotient. Degreewise harmonic finite dimensionality
  and vanishing of alternating forms above n leave a finite direct sum of
  odd harmonic spaces. This proves finiteness of the exact algebraic cokernel,
  rather than substituting an adjoint kernel or a completed quotient. -/
  have := finiteDimensional_totalFormHodgeLaplacian_ker g
  have : FiniteDimensional ℂ (oddHarmonicForms g) := by
    let T : oddHarmonicForms g →ₗ[ℂ] LinearMap.ker (totalFormHodgeLaplacian g) := {
      toFun u := ⟨u.val.val, u.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    apply FiniteDimensional.of_injective T
    intro u v h
    have heq : u.val.val = v.val.val :=
      congrArg (fun w : LinearMap.ker (totalFormHodgeLaplacian g) ↦ w.val) h
    exact Subtype.ext (Subtype.ext heq)
  exact (oddHarmonicCokernelEquiv g).finiteDimensional

end AtiyahSinger
