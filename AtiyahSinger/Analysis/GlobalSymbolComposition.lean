/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbol

/-!
# Composition in the global principal symbol quotient

Public module ID: M0679.

The fiberwise Hom product underlying SG III.3.10 and III.3.18-3.19.
Composition is the actual complex-linear composition at the same point and covector.
The order of arguments is output factor after input factor, with output order l+m.
A lower-order change in either factor changes the product by one lower order, so
this formula descends to the actual global symbol quotients. No homogeneous leading
representative, compact base, density, or metric is needed for this filtered algebra.
The comparison with operator composition is in GlobalComposition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F G : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin k)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin k)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin k)) G]

/-- Fiberwise composition of actual Hom-valued functions at the same cotangent vector. -/
def globalSymbolComp (b : GlobalSymbolFunction (n := n) F G)
    (a : GlobalSymbolFunction (n := n) E F) : GlobalSymbolFunction (n := n) E G :=
  fun x ξ ↦ (b x ξ).comp (a x ξ)

/-- Composition commutes with coordinates wherever the intermediate frame is valid. -/
theorem globalSymbolInChart_globalSymbolComp
    (b : GlobalSymbolFunction (n := n) F G) (a : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    (g : Trivialization (EuclideanSpace ℂ (Fin k)) (π (EuclideanSpace ℂ (Fin k)) G))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] [MemTrivializationAtlas g]
    (z η : EuclideanSpace ℝ (Fin n)) (hf : c.symm z ∈ f.baseSet) :
    globalSymbolInChart E G (globalSymbolComp b a) c e g z η =
      symbolComp (globalSymbolInChart F G b c f g)
        (globalSymbolInChart E F a c e f) z η := by
  /- Both expressions use the same point c.symm z and the same pulled-back covector.
  In the right-hand composite, f.continuousLinearMapAt followed by f.symmL cancel
  as an endomorphism of the actual intermediate fiber, using hf. Associativity
  gives the displayed formula. No chart derivative inverse or smoothness is used. -/
  -- The intermediate frame and its inverse cancel on this same actual fiber.
  have hcancel := f.symmL_continuousLinearMapAt (R := ℂ) hf
  ext v
  simp only [globalSymbolInChart, globalSymbolComp, symbolComp,
    ContinuousLinearMap.comp_apply]
  rw [hcancel]

/-- Fiberwise composition adds the orders of global symbols, including unequal fiber ranks. -/
theorem IsGlobalSymbol.globalSymbolComp {l m : ℝ}
    {b : GlobalSymbolFunction (n := n) F G} {a : GlobalSymbolFunction (n := n) E F}
    (hb : IsGlobalSymbol (n := n) (r := q) (q := k) F G l b)
    (ha : IsGlobalSymbol (n := n) (r := r) (q := q) E F m a) :
    IsGlobalSymbol (n := n) (r := r) (q := k) E G (l + m) (globalSymbolComp b a) := by
  /- Stage 1: fix any base chart and outer frames. Near each point choose an atlas
  frame of F. The preceding identity expresses the product by two local symbols;
  their mixed Leibniz estimate gives order l+m, with j frequency derivatives split
  between them. Joint real smoothness is local as well.
  Stage 2: for a compact coordinate set choose finitely many smaller compact
  neighborhoods inside these middle-frame domains. Combine the estimates on them.
  No globally valid middle frame or compactness of the entire base is required. -/
  classical
  intro c hc e g _ _
  let U := symbolChartDomain E G c e g
  let p := globalSymbolInChart E G (AtiyahSinger.globalSymbolComp b a) c e g
  have hU : IsOpen U := isOpen_symbolChartDomain E G c e g
  -- Equality on an open domain preserves the actual total mixed derivatives there.
  have hcongr {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
      (p₁ p₂ : SymbolFunction n r k) (hp₁ : IsSymbol V (l + m) p₁)
      (heq : ∀ z ∈ V, ∀ η, p₁ z η = p₂ z η) : IsSymbol V (l + m) p₂ := by
    refine ⟨hp₁.1.congr (fun z hz ↦ (heq z.1 hz.1 z.2).symm), ?_⟩
    intro K hKV hK i j
    obtain ⟨C, hC, hbound⟩ := hp₁.2 K hKV hK i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (p₁ y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (p₂ y) ξ) := by
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      rw [funext (heq y hy)]
    have hder := (hnear.iteratedFDeriv ℝ i).eq_of_nhds
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← hder]
    exact hbound x hx ξ
  -- A middle frame is chosen only near each base point, with its own valid overlap.
  have hlocal (z : U) : ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ z.val ∈ V ∧ IsSymbol V (l + m) p := by
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F (c.symm z.val)
    let V := symbolChartDomain E F c e f ∩ symbolChartDomain F G c f g
    have hf : c.symm z.val ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
    have hV : IsOpen V := (isOpen_symbolChartDomain E F c e f).inter
      (isOpen_symbolChartDomain F G c f g)
    have hzV : z.val ∈ V := ⟨⟨⟨z.property.1.1, z.property.1.2⟩, hf⟩,
      ⟨⟨z.property.1.1, hf⟩, z.property.2⟩⟩
    have ha' : IsSymbol V m (globalSymbolInChart E F a c e f) := by
      refine ⟨(ha c hc e f).1.mono (Set.prod_mono Set.inter_subset_left subset_rfl), ?_⟩
      intro K hK hcompact i j
      exact (ha c hc e f).2 K (hK.trans Set.inter_subset_left) hcompact i j
    have hb' : IsSymbol V l (globalSymbolInChart F G b c f g) := by
      refine ⟨(hb c hc f g).1.mono (Set.prod_mono Set.inter_subset_right subset_rfl), ?_⟩
      intro K hK hcompact i j
      exact (hb c hc f g).2 K (hK.trans Set.inter_subset_right) hcompact i j
    refine ⟨V, hV, hzV, hcongr hV _ _ (hb'.symbolComp hV ha') ?_⟩
    intro x hx ξ
    exact (globalSymbolInChart_globalSymbolComp b a c e f g x ξ hx.1.2).symm
  choose V hV hzV hpV using hlocal
  -- Smoothness is local; no smoothness of a globally selected middle frame is needed.
  refine ⟨?_, ?_⟩
  · intro z hz
    exact ((hpV ⟨z.1, hz.1⟩).1.contDiffAt
      (((hV ⟨z.1, hz.1⟩).prod isOpen_univ).mem_nhds
        ⟨hzV ⟨z.1, hz.1⟩, Set.mem_univ z.2⟩)).contDiffWithinAt
  · intro K hKU hK i j
    -- Smaller compact neighborhoods permit finitely many original local symbol estimates.
    choose L hL hzL hLV using fun z : U ↦ exists_compact_subset (hV z) (hzV z)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : U ↦ interior (L z))
      (fun _ ↦ isOpen_interior) (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hzL ⟨x, hKU hx⟩⟩)
    choose C hC hbound using fun z : U ↦ (hpV z).2 (L z) (hLV z) (hL z) i j
    refine ⟨∑ z ∈ t, C z, Finset.sum_nonneg (fun z _ ↦ hC z), ?_⟩
    intro x hx ξ
    obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
    apply (hbound z x (interior_subset hxz) ξ).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun z _ ↦ hC z) hzt

/-- Actual fiberwise composition packaged in the global symbol submodule. -/
def globalSymbolSpaceComp {l m : ℝ}
    (b : globalSymbolSpace (n := n) (r := q) (q := k) F G l)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalSymbolSpace (n := n) (r := r) (q := k) E G (l + m) :=
  ⟨globalSymbolComp b.val a.val, b.property.globalSymbolComp a.property⟩

/-- Changing either global symbol by one lower order preserves the product's principal class. -/
theorem globalPrincipalSymbolClass_comp_congr {l m : ℝ}
    (b b' : globalSymbolSpace (n := n) (r := q) (q := k) F G l)
    (a a' : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hb : globalPrincipalSymbolClass F G l b = globalPrincipalSymbolClass F G l b')
    (ha : globalPrincipalSymbolClass E F m a = globalPrincipalSymbolClass E F m a') :
    globalPrincipalSymbolClass E G (l + m) (globalSymbolSpaceComp b a) =
      globalPrincipalSymbolClass E G (l + m) (globalSymbolSpaceComp b' a') := by
  /- Write ba-b'a' as (b-b')a + b'(a-a') in every actual Hom fiber, retaining
  the order of factors. The two differences have orders l-1 and m-1 by quotient
  equality. Composition and addition put the result in order l+m-1. The global
  quotient equality criterion then gives the claim, without using quantization. -/
  -- The original quotient equalities supply the actual one-order-lower differences.
  have hb' := (globalPrincipalSymbolClass_eq_iff F G l b b').mp hb
  have ha' := (globalPrincipalSymbolClass_eq_iff E F m a a').mp ha
  have hleft : IsGlobalSymbol (r := r) (q := k) E G (l + m - 1)
      (globalSymbolComp (b.val - b'.val) a.val) := by
    convert hb'.globalSymbolComp a.property using 1
    ring
  have hright : IsGlobalSymbol (r := r) (q := k) E G (l + m - 1)
      (globalSymbolComp b'.val (a.val - a'.val)) := by
    convert b'.property.globalSymbolComp ha' using 1
    ring
  -- Expand in the actual Hom fibers while retaining the noncommutative factor order.
  apply (globalPrincipalSymbolClass_eq_iff E G (l + m) _ _).mpr
  change IsGlobalSymbol E G (l + m - 1)
    (globalSymbolComp b.val a.val - globalSymbolComp b'.val a'.val)
  have hexpand : globalSymbolComp b.val a.val - globalSymbolComp b'.val a'.val =
      globalSymbolComp (b.val - b'.val) a.val + globalSymbolComp b'.val (a.val - a'.val) := by
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    simp only [globalSymbolComp, Pi.sub_apply, Pi.add_apply, sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hexpand]
  exact hleft.add hright

/-- Fiberwise composition descended through both actual global principal-symbol quotients. -/
def globalPrincipalSymbolComp {l m : ℝ} :
    GlobalPrincipalSymbolSpace (n := n) (r := q) (q := k) F G l →
      GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m →
        GlobalPrincipalSymbolSpace (n := n) (r := r) (q := k) E G (l + m) :=
  Quotient.lift₂
    (fun b a ↦ globalPrincipalSymbolClass E G (l + m) (globalSymbolSpaceComp b a))
    (fun b a b' a' hb ha ↦ globalPrincipalSymbolClass_comp_congr b b' a a'
      (Quotient.sound hb) (Quotient.sound ha))

/-- The quotient product is computed by the actual fiberwise product of any representatives. -/
theorem globalPrincipalSymbolComp_class {l m : ℝ}
    (b : globalSymbolSpace (n := n) (r := q) (q := k) F G l)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolComp (globalPrincipalSymbolClass F G l b)
        (globalPrincipalSymbolClass E F m a) =
      globalPrincipalSymbolClass E G (l + m) (globalSymbolSpaceComp b a) := by
  /- Evaluate the two quotient lifts on the given representatives. The congruence
  theorem supplies well-definedness only; the chosen result is precisely the class
  of the actual composite. There is no extra representative-selection operation. -/
  -- Both quotient lifts evaluate on these exact original representatives.
  rfl

/-- The quotient product is additive in its output factor. -/
theorem globalPrincipalSymbolComp_add_left {l m : ℝ}
    (b b' : GlobalPrincipalSymbolSpace (n := n) (r := q) (q := k) F G l)
    (a : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolComp (b + b') a =
      globalPrincipalSymbolComp b a + globalPrincipalSymbolComp b' a := by
  /- Choose representatives by quotient surjectivity. Fiberwise composition
  distributes over addition in the output map. Both the symbol submodule and its
  quotient use this pointwise sum, and the class projection preserves it. -/
  -- Select actual order-l and order-m representatives of the three original classes.
  obtain ⟨b, rfl⟩ := globalPrincipalSymbolClass_surjective F G l b
  obtain ⟨b', rfl⟩ := globalPrincipalSymbolClass_surjective F G l b'
  obtain ⟨a, rfl⟩ := globalPrincipalSymbolClass_surjective E F m a
  rw [← map_add, globalPrincipalSymbolComp_class, globalPrincipalSymbolComp_class,
    globalPrincipalSymbolComp_class, ← map_add]
  -- Distribute the output map before taking its principal class.
  rfl

/-- The quotient product is additive in its input factor. -/
theorem globalPrincipalSymbolComp_add_right {l m : ℝ}
    (b : GlobalPrincipalSymbolSpace (n := n) (r := q) (q := k) F G l)
    (a a' : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolComp b (a + a') =
      globalPrincipalSymbolComp b a + globalPrincipalSymbolComp b a' := by
  /- On arbitrary representatives, the output linear map sends the sum of the
  two input images to the sum of their images. Project the resulting equality
  of actual global symbols, then use quotient surjectivity for all three factors. -/
  -- Quotient surjectivity reduces the claim to the original symbol functions.
  obtain ⟨b, rfl⟩ := globalPrincipalSymbolClass_surjective F G l b
  obtain ⟨a, rfl⟩ := globalPrincipalSymbolClass_surjective E F m a
  obtain ⟨a', rfl⟩ := globalPrincipalSymbolClass_surjective E F m a'
  rw [← map_add, globalPrincipalSymbolComp_class, globalPrincipalSymbolComp_class,
    globalPrincipalSymbolComp_class, ← map_add]
  -- Additivity of the same output map distributes over the two input images.
  congr 1
  apply Subtype.ext
  funext x ξ
  apply ContinuousLinearMap.ext
  intro v
  simp [globalSymbolSpaceComp, globalSymbolComp]

/-- Complex scalars pass through the output factor without conjugation. -/
theorem globalPrincipalSymbolComp_smul_left {l m : ℝ} (z : ℂ)
    (b : GlobalPrincipalSymbolSpace (n := n) (r := q) (q := k) F G l)
    (a : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolComp (z • b) a = z • globalPrincipalSymbolComp b a := by
  /- On representatives, multiplying the output linear map by z multiplies the
  composite by z. The complex-linear projection carries this identity to classes.
  Surjectivity removes the choice of representatives. No adjoint occurs here. -/
  -- Choose representatives without replacing the original actual fiber maps.
  obtain ⟨b, rfl⟩ := globalPrincipalSymbolClass_surjective F G l b
  obtain ⟨a, rfl⟩ := globalPrincipalSymbolClass_surjective E F m a
  rw [← map_smul, globalPrincipalSymbolComp_class, globalPrincipalSymbolComp_class,
    ← map_smul]
  -- Scaling the output map scales the composite by the same complex scalar.
  rfl

/-- Complex scalars pass through the input factor by complex linearity of the output map. -/
theorem globalPrincipalSymbolComp_smul_right {l m : ℝ} (z : ℂ)
    (b : GlobalPrincipalSymbolSpace (n := n) (r := q) (q := k) F G l)
    (a : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolComp b (z • a) = z • globalPrincipalSymbolComp b a := by
  /- For actual representatives b(z a(v)) = z b(a(v)) in each complex fiber.
  Apply the class projection and then descend by quotient surjectivity. This
  is complex bilinearity, not the conjugate-linearity of a Hermitian adjoint. -/
  -- Descend the complex-linear identity from actual order-l and order-m symbols.
  obtain ⟨b, rfl⟩ := globalPrincipalSymbolClass_surjective F G l b
  obtain ⟨a, rfl⟩ := globalPrincipalSymbolClass_surjective E F m a
  rw [← map_smul, globalPrincipalSymbolComp_class, globalPrincipalSymbolComp_class,
    ← map_smul]
  -- Complex linearity of the same output map introduces no scalar conjugation.
  congr 1
  apply Subtype.ext
  funext x ξ
  apply ContinuousLinearMap.ext
  intro v
  simp [globalSymbolSpaceComp, globalSymbolComp]

end AtiyahSinger
