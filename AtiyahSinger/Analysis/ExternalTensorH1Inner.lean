/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorL2
public import AtiyahSinger.Analysis.GeometricTensorSobolev

/-!
# The first Sobolev inner product on separated coordinate tensors

Public module ID: M0612.

Fubini identifies the original tensor-coordinate L2 pairing. The scaled first
coordinate derivatives split into the two factor directions, so the first
Bessel pairing is exactly the sum of the two mixed pairings minus their common
zeroth-order part. This identity controls finite sums of tensors, including
cross terms; a bound on individual pure tensors would not suffice.

The coordinates and Fourier normalization are the ones used by the original
product presentation. The theorem makes no positivity assumption on dimensions
or ranks. All coordinate computations are local parts of this single identity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped SchwartzMap

set_option maxSynthPendingDepth 30

variable {n m r s : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin m)
local notation "Z" => EuclideanSpace ℝ (Fin (n + m))
local notation "U" => EuclideanSpace ℂ (Fin r)
local notation "V" => EuclideanSpace ℂ (Fin s)
local notation "W" => EuclideanSpace ℂ (Fin (r * s))

set_option maxHeartbeats 1000000 in
-- Combine the tensor L2 pairing with the two families of scaled coordinate derivatives.
/-- The first Bessel pairing is the sum of the mixed energies minus their common L2 part. -/
theorem inner_schwartzSobolevCoordinate_one_tensor
    (u u' : 𝓢(X, U)) (v v' : 𝓢(Y, V)) (w w' : 𝓢(Z, W))
    (hw : ∀ (x : X) (y : Y) (a : Fin r) (b : Fin s),
      w (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (a, b)) =
        u x a * v y b)
    (hw' : ∀ (x : X) (y : Y) (a : Fin r) (b : Fin s),
      w' (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (a, b)) =
        u' x a * v' y b) :
    inner ℂ (schwartzSobolevCoordinate 1 w) (schwartzSobolevCoordinate 1 w') =
      inner ℂ (schwartzSobolevCoordinate 1 u) (schwartzSobolevCoordinate 1 u') *
          inner ℂ (v.toLp 2) (v'.toLp 2) +
        inner ℂ (u.toLp 2) (u'.toLp 2) *
          inner ℂ (schwartzSobolevCoordinate 1 v) (schwartzSobolevCoordinate 1 v') -
        inner ℂ (u.toLp 2) (u'.toLp 2) * inner ℂ (v.toLp 2) (v'.toLp 2) := by
  classical
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  -- Fubini factors the exact finite tensor-coordinate pairing.
  have hL2
      (u u' : 𝓢(X, U)) (v v' : 𝓢(Y, V)) (w w' : 𝓢(Z, W))
      (hw : ∀ (x : X) (y : Y) (a : Fin r) (b : Fin s),
        w (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (a, b)) =
          u x a * v y b)
      (hw' : ∀ (x : X) (y : Y) (a : Fin r) (b : Fin s),
        w' (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (a, b)) =
          u' x a * v' y b) :
      inner ℂ (w.toLp 2) (w'.toLp 2) =
        inner ℂ (u.toLp 2) (u'.toLp 2) * inner ℂ (v.toLp 2) (v'.toLp 2) := by
    classical
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    have he : MeasurePreserving e := by
      exact (WithLp.volume_preserving_ofLp X Y).comp
        ((LinearIsometryEquiv.measurePreserving
          (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m ↦ ℝ))).comp
          (LinearIsometryEquiv.measurePreserving
            (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm)))
    have hpoint (x : X) (y : Y) :
        inner ℂ (w (e.symm (x, y))) (w' (e.symm (x, y))) =
          inner ℂ (u x) (u' x) * inner ℂ (v y) (v' y) := by
      rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply]
      rw [← finProdFinEquiv.sum_comp]
      simp only [Fintype.sum_prod_type, RCLike.inner_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [show w (e.symm (x, y)) (finProdFinEquiv (a, b)) = _ from hw x y a b,
        show w' (e.symm (x, y)) (finProdFinEquiv (a, b)) = _ from hw' x y a b, map_mul]
      ring
    rw [SchwartzMap.inner_toL2_toL2_eq w w' volume,
      SchwartzMap.inner_toL2_toL2_eq u u' volume,
      SchwartzMap.inner_toL2_toL2_eq v v' volume]
    have he' : MeasurePreserving e.toHomeomorph.toMeasurableEquiv := he
    rw [← he'.symm.integral_comp' (fun z : Z ↦ inner ℂ (w z) (w' z))]
    change (∫ z : X × Y, inner ℂ (w (e.symm z)) (w' (e.symm z))) = _
    simp_rw [hpoint]
    exact integral_prod_mul (μ := volume) (ν := volume) (L := ℂ)
      (fun x ↦ inner ℂ (u x) (u' x)) (fun y ↦ inner ℂ (v y) (v' y))
  -- Polarization transports the already proved Bessel graph norm identity.
  have hH1 {d k : ℕ}
      (u v : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin k))) :
      inner ℂ (schwartzSobolevCoordinate 1 u) (schwartzSobolevCoordinate 1 v) =
        inner ℂ (u.toLp 2) (v.toLp 2) + (((2 * Real.pi)⁻¹ : ℂ) ^ 2) *
          ∑ a : Fin d, inner ℂ
            ((LineDeriv.lineDerivOp (EuclideanSpace.single a (1 : ℝ)) u).toLp 2)
            ((LineDeriv.lineDerivOp (EuclideanSpace.single a (1 : ℝ)) v).toLp 2) := by
    let J := schwartzH1Jet d k
    let H := schwartzSobolevCoordinateLinearMap d k 1
    have hnorm (f : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin k))) :
        ‖J f‖ = ‖H f‖ := norm_schwartzH1Jet d k f
    have hinner : inner ℂ (H u) (H v) = inner ℂ (J u) (J v) := by
      simp only [inner_eq_sum_norm_sq_div_four, ← map_add, ← map_sub, ← map_smul, hnorm]
    change inner ℂ (H u) (H v) = _
    rw [hinner, PiLp.inner_apply]
    have heval (f : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin k)))
        (a : Option (Fin d)) : (J f).ofLp a =
        match a with
        | none => f.toLp 2
        | some i => ((2 * Real.pi)⁻¹ : ℂ) •
            (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f).toLp 2 := by
      cases a <;> rfl
    simp only [heval, Fintype.sum_option]
    simp only [inner_smul_left, inner_smul_right, map_inv₀, map_mul, map_ofNat,
      Complex.conj_ofReal]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  -- Differentiate the actual coordinate identity in an arbitrary product direction.
  have hderiv
      (u : 𝓢(X, U)) (v : 𝓢(Y, V)) (w : 𝓢(Z, W))
      (hw : ∀ (x : X) (y : Y) (a : Fin r) (b : Fin s),
        w (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (a, b)) =
          u x a * v y b)
      (tx : X) (ty : Y) (x : X) (y : Y) (a : Fin r) (b : Fin s) :
      (LineDeriv.lineDerivOp
          ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm (tx, ty)) w)
          (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (a, b)) =
        u x a * (LineDeriv.lineDerivOp ty v) y b +
          v y b * (LineDeriv.lineDerivOp tx u) x a := by
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    let pr : W →L[ℝ] ℂ :=
      (EuclideanSpace.proj (𝕜 := ℂ) (finProdFinEquiv (a, b))).restrictScalars ℝ
    let pa : U →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) a).restrictScalars ℝ
    let pb : V →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) b).restrictScalars ℝ
    have hout := pr.hasFDerivAt.comp (x, y)
      ((w.differentiableAt (x := e.symm (x, y))).hasFDerivAt.comp (x, y)
        e.symm.toContinuousLinearMap.hasFDerivAt)
    have hleft := pa.hasFDerivAt.comp (x, y)
      ((u.differentiableAt (x := x)).hasFDerivAt.comp (x, y)
        (ContinuousLinearMap.fst ℝ X Y).hasFDerivAt)
    have hright := pb.hasFDerivAt.comp (x, y)
      ((v.differentiableAt (x := y)).hasFDerivAt.comp (x, y)
        (ContinuousLinearMap.snd ℝ X Y).hasFDerivAt)
    have hfun : (fun z : X × Y ↦ pr (w (e.symm z))) =
        fun z : X × Y ↦ pa (u z.1) * pb (v z.2) :=
      funext (fun z ↦ hw z.1 z.2 a b)
    change HasFDerivAt (fun z : X × Y ↦ pr (w (e.symm z))) _ (x, y) at hout
    rw [hfun] at hout
    have heq := congrArg (fun L : X × Y →L[ℝ] ℂ ↦ L (tx, ty))
      (hout.unique (hleft.mul hright))
    change ((fderiv ℝ w (e.symm (x, y))) (e.symm (tx, ty))) (finProdFinEquiv (a, b)) =
      u x a * ((fderiv ℝ v y) ty) b + v y b * ((fderiv ℝ u x) tx) a at heq
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using heq
  -- The concatenation sends these two families to the original coordinate basis.
  have hbLeft (i : Fin n) :
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
        (EuclideanSpace.single i 1, 0) = EuclideanSpace.single (Fin.castAdd m i) 1 := by
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · ext j
      change (EuclideanSpace.single i (1 : ℝ)) j =
        (EuclideanSpace.single (Fin.castAdd m i) (1 : ℝ)) (Fin.castAdd m j)
      simp
    · ext j
      have hne : Fin.natAdd n j ≠ Fin.castAdd m i := by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
        omega
      change (0 : Y) j =
        (EuclideanSpace.single (Fin.castAdd m i) (1 : ℝ)) (Fin.natAdd n j)
      simp [hne]
  have hbRight (i : Fin m) :
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
        (0, EuclideanSpace.single i 1) = EuclideanSpace.single (Fin.natAdd n i) 1 := by
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · ext j
      have hne : Fin.castAdd m j ≠ Fin.natAdd n i := by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
        omega
      change (0 : X) j =
        (EuclideanSpace.single (Fin.natAdd n i) (1 : ℝ)) (Fin.castAdd m j)
      simp [hne]
    · ext j
      change (EuclideanSpace.single i (1 : ℝ)) j =
        (EuclideanSpace.single (Fin.natAdd n i) (1 : ℝ)) (Fin.natAdd n j)
      simp
  have hleft (u : 𝓢(X, U)) (v : 𝓢(Y, V)) (w : 𝓢(Z, W))
      (hh : ∀ (x : X) (y : Y) (a : Fin r) (b : Fin s),
        w (e.symm (x, y)) (finProdFinEquiv (a, b)) = u x a * v y b)
      (i : Fin n) (x : X) (y : Y) (a : Fin r) (b : Fin s) :
      (LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.castAdd m i) (1 : ℝ)) w)
          (e.symm (x, y)) (finProdFinEquiv (a, b)) =
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) u) x a * v y b := by
    have h := hderiv u v w hh (EuclideanSpace.single i 1) 0 x y a b
    rw [hbLeft i] at h
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, map_zero, PiLp.zero_apply,
      mul_zero, zero_mul, zero_add, mul_comm] using h
  have hright (u : 𝓢(X, U)) (v : 𝓢(Y, V)) (w : 𝓢(Z, W))
      (hh : ∀ (x : X) (y : Y) (a : Fin r) (b : Fin s),
        w (e.symm (x, y)) (finProdFinEquiv (a, b)) = u x a * v y b)
      (i : Fin m) (x : X) (y : Y) (a : Fin r) (b : Fin s) :
      (LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n i) (1 : ℝ)) w)
          (e.symm (x, y)) (finProdFinEquiv (a, b)) =
        u x a * (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) v) y b := by
    have h := hderiv u v w hh 0 (EuclideanSpace.single i 1) x y a b
    rw [hbRight i] at h
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, map_zero, PiLp.zero_apply,
      mul_zero, add_zero] using h
  -- Sum all the left and right derivative pairings, including their cross terms.
  have hIL (i : Fin n) :
      inner ℂ
        ((LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.castAdd m i) (1 : ℝ)) w).toLp 2)
        ((LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.castAdd m i) (1 : ℝ)) w').toLp 2) =
      inner ℂ ((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) u).toLp 2)
        ((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) u').toLp 2) *
          inner ℂ (v.toLp 2) (v'.toLp 2) :=
    hL2 _ _ _ _ _ _ (hleft u v w hw i) (hleft u' v' w' hw' i)
  have hIR (i : Fin m) :
      inner ℂ
        ((LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n i) (1 : ℝ)) w).toLp 2)
        ((LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n i) (1 : ℝ)) w').toLp 2) =
      inner ℂ (u.toLp 2) (u'.toLp 2) *
        inner ℂ ((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) v).toLp 2)
          ((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) v').toLp 2) :=
    hL2 _ _ _ _ _ _ (hright u v w hw i) (hright u' v' w' hw' i)
  rw [hH1 w w', hH1 u u', hH1 v v', hL2 u u' v v' w w' hw hw', Fin.sum_univ_add]
  simp_rw [hIL, hIR]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

end AtiyahSinger
