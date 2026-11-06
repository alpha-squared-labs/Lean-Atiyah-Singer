/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorSymbol
public import AtiyahSinger.Topology.SupportTripleTransport
public import Mathlib.Analysis.Complex.Basic

/-!
# The concrete exterior symbol on a complex line

Public module ID: M1567.

D10: in the standard even basis 1 and odd basis e of the exterior algebra of
the Hermitian complex line, wedge minus contraction has even-to-odd block z
and odd-to-even block -conj(z). The actual triple below uses multiplication by
z on the punctured plane and has exactly the compact control {0}.

Sources: SG's exterior/Clifford convention, as fixed in `ExteriorSymbol`;
Hatcher, Vector Bundles and K-Theory, Example 1.10, p.23, and Corollary 2.3,
pp.41--42. Hatcher's clutching convention depends on the ordered hemispheres.
No identification with his H - 1, oriented generator normalization, or Bott
periodicity is claimed here. Conjugation reverses this actual class by an
explicit radial homotopy of boundary maps, independently of such normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] trivialTopology isFiniteRank_trivial

/-- The punctured-line symbol and its inverse are continuous on the actual total spaces. -/
theorem bottLine_boundary_continuity :
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial ℂ (Fin 1 → ℂ)) ({0} : Set ℂ)ᶜ) ↦
        (⟨z.proj, z.proj.val • z.snd⟩ : TotalSpace Unit
          (Restrict (Bundle.Trivial ℂ (Fin 1 → ℂ)) ({0} : Set ℂ)ᶜ))) ∧
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial ℂ (Fin 1 → ℂ)) ({0} : Set ℂ)ᶜ) ↦
        (⟨z.proj, z.proj.val⁻¹ • z.snd⟩ : TotalSpace Unit
          (Restrict (Bundle.Trivial ℂ (Fin 1 → ℂ)) ({0} : Set ℂ)ᶜ))) := by
  /- Stage 1: in the restricted product trivializations the forward map is
  (z,v) ↦ (z,zv), continuous by joint complex multiplication.
  Stage 2: the inverse map is (z,v) ↦ (z,z⁻¹v). Inversion is continuous on
  the punctured plane. Transport these product maps through the same actual
  restriction topologies to obtain both certificates used by the triple. -/
  -- Read the original pullback topology through its two defining coordinates.
  let A := ({0} : Set ℂ)ᶜ
  let E := Bundle.Trivial ℂ (Fin 1 → ℂ)
  let f : A → ℂ := Subtype.val
  have hbase : Continuous (fun z : TotalSpace Unit (Restrict E A) ↦ z.proj) :=
    Pullback.continuous_proj Unit E f
  have hpoint : Continuous (fun z : TotalSpace Unit (Restrict E A) ↦ z.proj.val) :=
    continuous_subtype_val.comp hbase
  have hvector : Continuous (fun z : TotalSpace Unit (Restrict E A) ↦ z.snd) := by
    have hp : Continuous (fun z : TotalSpace Unit E ↦ (z.proj, z.snd)) :=
      continuous_induced_dom
    exact continuous_snd.comp (hp.comp (Pullback.continuous_lift Unit E f))
  have hinverse : Continuous (fun z : TotalSpace Unit (Restrict E A) ↦ z.proj.val⁻¹) :=
    hpoint.inv₀ (fun z ↦ by
      simpa only [A, Set.mem_compl_iff, Set.mem_singleton_iff] using z.proj.property)
  constructor
  · -- Multiplication is jointly continuous on the original punctured-line fibers.
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    apply hbase.prodMk
    apply continuous_induced_rng.mpr
    exact hpoint.prodMk (hpoint.smul hvector)
  · -- The same total-space coordinates use complex inversion off the zero section.
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    apply hbase.prodMk
    apply continuous_induced_rng.mpr
    exact hpoint.prodMk (hinverse.smul hvector)

/-- The complex-line exterior symbol with its actual multiplication boundary. -/
def bottLineTriple : CompactSupportTriple
    (Bundle.Trivial ℂ (Fin 1 → ℂ)) (Bundle.Trivial ℂ (Fin 1 → ℂ)) where
  control := {0}
  isCompact_control := isCompact_singleton
  boundary :=
    { linearEquiv := fun z ↦ LinearEquiv.smulOfNeZero ℂ (Fin 1 → ℂ) z.val (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.property)
      continuous_total := bottLine_boundary_continuity.1
      continuous_symm := bottLine_boundary_continuity.2 }

/-- The compact-support class of the specified complex-line exterior triple. -/
def bottLineClass : CompactSupportKZero ℂ :=
  bottLineTriple.compactSupportClass

/-- Wedge minus contraction on the complex line has blocks z and -conj(z). -/
theorem cliffordSymbol_complex_line (z a b : ℂ) :
    cliffordSymbol z (algebraMap ℂ (ExteriorAlgebra ℂ ℂ) a + ExteriorAlgebra.ι ℂ b) =
      ExteriorAlgebra.ι ℂ (z * a) -
        algebraMap ℂ (ExteriorAlgebra ℂ ℂ) (star z * b) := by
  /- Stage 1: contraction kills degree zero and wedge multiplication sends
  its scalar a to z*a in degree one. All degree-two elements vanish since
  the underlying complex vector space has dimension one.
  Stage 2: contraction of b*e by z*e is the Hermitian inner product
  conj(z)*b, since the first argument is conjugate-linear. Subtracting this
  term gives the stated negative odd-to-even block and fixes the convention
  for the multiplication-by-z boundary in bottLineTriple. -/
  -- In a one-dimensional space both vectors are scalar multiples of the same generator.
  have hwedge : ExteriorAlgebra.ι ℂ z * ExteriorAlgebra.ι ℂ b = 0 := by
    rw [show z = z • (1 : ℂ) by simp, show b = b • (1 : ℂ) by simp]
    rw [map_smul, map_smul, smul_mul_assoc, mul_smul_comm,
      ExteriorAlgebra.ι_sq_zero, smul_zero, smul_zero]
  -- Degree zero contributes wedge multiplication, while contraction sees the odd coefficient.
  change ExteriorAlgebra.ι ℂ z *
      (algebraMap ℂ (ExteriorAlgebra ℂ ℂ) a + ExteriorAlgebra.ι ℂ b) -
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ ℂ)) (innerₛₗ ℂ z)
        (algebraMap ℂ (ExteriorAlgebra ℂ ℂ) a + ExteriorAlgebra.ι ℂ b) = _
  rw [mul_add, hwedge, add_zero, map_add, CliffordAlgebra.contractLeft_algebraMap,
    CliffordAlgebra.contractLeft_ι, zero_add]
  have hscalar : ExteriorAlgebra.ι ℂ z * algebraMap ℂ (ExteriorAlgebra ℂ ℂ) a =
      ExteriorAlgebra.ι ℂ (z * a) := by
    rw [← Algebra.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      ← map_smul]
    congr 1
    exact mul_comm a z
  rw [hscalar]
  simp only [innerₛₗ_apply_apply, RCLike.inner_apply', RCLike.star_def]

set_option backward.isDefEq.respectTransparency.types false in
/-- Conjugating the base of the actual line symbol reverses its support class. -/
theorem compactSupportKZeroHomeomorph_conj_bottLineClass :
    compactSupportKZeroHomeomorph Complex.conjCLE.toHomeomorph bottLineClass =
      -bottLineClass := by
  /- Stage 1: the actual homeomorphism transport is pullback along the inverse
  conjugation map, which is conjugation itself. The canonical trivial-bundle
  identifications retain the boundary v ↦ conj(z)*v and control {0}.
  Stage 2: on the punctured plane, interpolate from z⁻¹ to conj(z) by the
  scalar ((1-t) + t*‖z‖²)*z⁻¹. Its real prefactor is strictly positive for
  0 ≤ t ≤ 1 and z ≠ 0. Thus this is a continuous family of isomorphisms,
  all with the single compact control {0}, including continuous inverses.
  Stage 3: homotopy invariance identifies this class with the class of the
  inverse original triple. The raw-triple inverse formula gives its negative.
  No sphere orientation, generator theorem, or periodicity is used. -/
  classical
  let E := Bundle.Trivial ℂ (Fin 1 → ℂ)
  let f : C(ℂ, ℂ) :=
    ⟨Complex.conjCLE.toHomeomorph.symm,
      Complex.conjCLE.toHomeomorph.symm.continuous⟩
  let hf : IsProperMap f := Complex.conjCLE.toHomeomorph.symm.isProperMap
  let a := bottLineTriple
  let e := pullbackTrivialIso f 1
  let : IsFiniteRank ((f : ℂ → ℂ) *ᵖ E) := isFiniteRank_pullback f
  let b : CompactSupportTriple E E := (a.pullback f hf).congr e e
  -- Pull back along the actual inverse conjugation and retain its original vectors.
  have he (x : ℂ) (v : Fin 1 → ℂ) : e.linearEquiv x v = v :=
    pullbackTrivialIso_apply f 1 x v
  have hei (x : ℂ) (v : Fin 1 → ℂ) : e.symm.linearEquiv x v = v := by
    exact (he x ((e.linearEquiv x).symm v)).symm.trans
      ((e.linearEquiv x).apply_symm_apply v)
  have hcontrol : b.control ⊆ ({0} : Set ℂ) := by
    intro z hz
    change f z ∈ ({0} : Set ℂ) at hz
    have hz' : star z = (0 : ℂ) := hz
    simpa using congrArg star hz'
  have hboundary (z : (b.controlᶜ : Set ℂ)) (v : Fin 1 → ℂ) :
      b.boundary.linearEquiv z v = star z.val • v := by
    rw [CompactSupportTriple.congr_apply, hei]
    change (f ⁻¹' a.controlᶜ : Set ℂ) at z
    change e.linearEquiv z.val ((a.boundary.pullback f).linearEquiv z v) = _
    rw [RelativeTriple.pullback_apply, he]
    rfl
  -- A single positive radial path joins the inverse boundary to the pulled boundary.
  let U : Set ℂ := ({0} : Set ℂ)ᶜ
  have hne (z : U) : z.val ≠ 0 := by
    simpa only [U, Set.mem_compl_iff, Set.mem_singleton_iff] using z.property
  let r (t : unitInterval) (z : U) : ℝ := (1 - (t : ℝ)) + (t : ℝ) * ‖z.val‖ ^ 2
  have hr (t : unitInterval) (z : U) : 0 < r t z := by
    have hz : 0 < ‖z.val‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (hne z))
    by_cases ht : (t : ℝ) = 1
    · simpa [r, ht] using hz
    · have ht' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
      exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht')
        (mul_nonneg t.property.1 (sq_nonneg _))
  let c : C(unitInterval × U, ℂ) :=
    ⟨fun p ↦ (r p.1 p.2 : ℂ) * p.2.val⁻¹, by
      have hz : Continuous (fun p : unitInterval × U ↦ p.2.val) :=
        continuous_subtype_val.comp continuous_snd
      have ht : Continuous (fun p : unitInterval × U ↦ (p.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      exact (Complex.continuous_ofReal.comp
        ((continuous_const.sub ht).add (ht.mul (hz.norm.pow 2)))).mul
        (hz.inv₀ (fun p ↦ hne p.2))⟩
  have hc (p : unitInterval × U) : c p ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hr p.1 p.2)))
      (inv_ne_zero (hne p.2))
  have hc₀ (z : U) : c (0, z) = z.val⁻¹ := by simp [c, r]
  have hc₁ (z : U) : c (1, z) = star z.val := by
    change (((1 - (1 : ℝ)) + 1 * ‖z.val‖ ^ 2 : ℝ) : ℂ) * z.val⁻¹ = _
    simp only [sub_self, one_mul, zero_add, Complex.ofReal_pow]
    rw [← Complex.conj_mul', mul_assoc, mul_inv_cancel₀ (hne z), mul_one]
    rfl
  -- The original iterated pullback topology supplies joint continuity, including the inverse.
  let q : C(unitInterval × U, U) := ⟨Prod.snd, continuous_snd⟩
  let P := (q : unitInterval × U → U) *ᵖ (Restrict E U)
  let : IsFiniteRank (Restrict E U) := isFiniteRank_restrict U
  let : IsFiniteRank P := isFiniteRank_pullback q
  let p : C(TotalSpace Unit P, unitInterval × U) := ⟨fun z ↦ z.proj, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit P → unitInterval × U) *ᵖ P) :=
    isFiniteRank_pullback p
  have hvector : Continuous (fun z : TotalSpace Unit P ↦
      (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit P → unitInterval × U) *ᵖ P))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit P p).continuous_iff]
    exact continuous_id.prodMk continuous_id
  have hscale := continuous_smul_section
    ((p : TotalSpace Unit P → unitInterval × U) *ᵖ P)
    (c.comp p) (fun z ↦ z.snd) hvector
  let m : Hom P P :=
    { linearMap := fun x ↦ c x • LinearMap.id
      continuous_total := by
        change Continuous (fun z : TotalSpace Unit P ↦
          (⟨z.proj, c z.proj • z.snd⟩ : TotalSpace Unit P))
        exact (Pullback.continuous_lift Unit P p).comp hscale }
  let path : Iso P P := m.toIso (fun x ↦
    (LinearEquiv.smulOfNeZero ℂ (P x) (c x) (hc x)).bijective)
  have ha : a.inverse.control ⊆ ({0} : Set ℂ) := fun _ hz ↦ hz
  have hhom : a.inverse.Homotopic b := by
    refine ⟨{0}, isCompact_singleton, ha, hcontrol, ?_⟩
    refine ⟨{ iso := path, map_zero := ?_, map_one := ?_ }⟩
    · intro z v
      change U at z
      change E z at v
      change c (0, z) • v = _
      rw [hc₀, CompactSupportTriple.enlarge_apply]
      rfl
    · intro z v
      change U at z
      change E z at v
      change c (1, z) • v = _
      rw [hc₁, CompactSupportTriple.enlarge_apply, hboundary]
  -- Only controlled homotopy, actual bundle conjugation and raw-triple inversion are used.
  calc
    compactSupportKZeroHomeomorph Complex.conjCLE.toHomeomorph bottLineClass =
        (a.pullback f hf).compactSupportClass :=
      (a.compactSupportClass_pullback f hf).symm
    _ = b.compactSupportClass := ((a.pullback f hf).compactSupportClass_congr e e).symm
    _ = a.inverse.compactSupportClass :=
      (a.inverse.compactSupportClass_eq_of_homotopic b hhom).symm
    _ = -bottLineClass := a.compactSupportClass_inverse

end AtiyahSinger
