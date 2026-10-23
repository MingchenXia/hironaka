import DeJongAlterations.Algebra.NodeFamilyFlat
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Algebra of the node model `R[u,v]/(uv - h)`

Commutative algebra for the computation of the dualizing sheaf of the node model (blueprint
`sm-omega.tex`, `lem:sm-omega-node-equalizer`, `lem:sm-omega-node-kaehler`). Throughout, `A` is a
ring with elements `u, v`.

## Equalizer (`B_u ∩ B_v = B`)

* `NodeEqualizerData u v`: `u` and `v` are non-zero-divisors and `v` is a non-zero-divisor
  modulo `u`.
* `NodeEqualizerData.mem_of_pow_mul_mem`: then `vᵐ x ∈ (uⁿ)` implies `x ∈ (uⁿ)`.
* `NodeEqualizerData.exists_eq`: if `a ∈ A_u` and `b ∈ A_v` have the same image in `A_{uv}`, they
  come from a common `c ∈ A`.
* `NodeEqualizerData.isLocalization`: the data pass to every localization of `A`.
* `nodeEqualizerData_node`: the node algebra `R[u,v]/(uv - h)` satisfies them when `h` is a
  non-zero-divisor of `R` (flatness, from Codex's `NodeFamilyFlat.node_flat`, and the quotient
  `R[u,v]/(uv - h, u) ≅ (R/h)[v]`).

## Kähler differentials

* `extendDerivation`: derivations into a localization extend to the localization.
* `bijective_smul_D_of_span`: if `Ω_{S/R}` is spanned by `ds` and some derivation sends `s` to
  `1`, then `c ↦ c • ds` is an isomorphism `S ≅ Ω_{S/R}`.
* `nodeKaehler_bijective`: for every localization `S` of the node algebra in which `u` is a unit,
  `Ω_{S/R}` is free on `du`.
-/

noncomputable section

open Polynomial

universe u

namespace DeJongAlterations.StableModification.Omega

section Equalizer

variable {A : Type u} [CommRing A]

/-- The hypotheses under which `A = A_u ∩ A_v` inside `A_{uv}`: `u, v` are non-zero-divisors
and `v` is a non-zero-divisor on `A/(u)`. -/
structure NodeEqualizerData (u v : A) : Prop where
  u_mem : u ∈ nonZeroDivisors A
  v_mem : v ∈ nonZeroDivisors A
  sat : ∀ x : A, v * x ∈ Ideal.span {u} → x ∈ Ideal.span {u}

namespace NodeEqualizerData

variable {u v : A} (H : NodeEqualizerData u v)
include H

theorem pow_mem_span_one (m : ℕ) (x : A) (hx : v ^ m * x ∈ Ideal.span {u}) :
    x ∈ Ideal.span {u} := by
  induction m generalizing x with
  | zero => simpa using hx
  | succ m ih =>
    apply ih
    apply H.sat
    rw [← mul_assoc, ← pow_succ']
    exact hx

/-- `vᵐ x ∈ (uⁿ)` implies `x ∈ (uⁿ)`. -/
theorem mem_of_pow_mul_mem (n m : ℕ) (x : A) (hx : v ^ m * x ∈ Ideal.span {u ^ n}) :
    x ∈ Ideal.span {u ^ n} := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have h1 : v ^ m * x ∈ Ideal.span {u} :=
      Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self u n.succ_ne_zero) hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp (H.pow_mem_span_one m x h1)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hx
    have hyz : v ^ m * y = z * u ^ n := by
      apply (mul_cancel_right_mem_nonZeroDivisors H.u_mem).mp
      rw [pow_succ] at hz
      linear_combination hz.symm
    have := ih y (Ideal.mem_span_singleton'.mpr ⟨z, hyz.symm⟩)
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp this
    exact Ideal.mem_span_singleton'.mpr ⟨w, by ring⟩

/-- **`A = A_u ∩ A_v`.** If `a ∈ A_u` and `b ∈ A_v` have the same image in `A_{uv}`, then both
come from one element of `A`. -/
theorem exists_eq {Au Av Auv : Type*} [CommRing Au] [CommRing Av] [CommRing Auv]
    [Algebra A Au] [Algebra A Av] [Algebra A Auv] [IsLocalization.Away u Au]
    [IsLocalization.Away v Av] [IsLocalization.Away (u * v) Auv]
    (ρu : Au →+* Auv) (ρv : Av →+* Auv) (hρu : ρu.comp (algebraMap A Au) = algebraMap A Auv)
    (hρv : ρv.comp (algebraMap A Av) = algebraMap A Auv) (a : Au) (b : Av)
    (hab : ρu a = ρv b) : ∃ c : A, algebraMap A Au c = a ∧ algebraMap A Av c = b := by
  obtain ⟨⟨α, s⟩, hα⟩ := IsLocalization.surj (Submonoid.powers u) a
  obtain ⟨⟨β, t⟩, hβ⟩ := IsLocalization.surj (Submonoid.powers v) b
  obtain ⟨n, hn⟩ := s.2
  obtain ⟨m, hm⟩ := t.2
  simp only at hα hβ
  rw [← hn] at hα
  rw [← hm] at hβ
  have e1 : ρu a * algebraMap A Auv (u ^ n) = algebraMap A Auv α := by
    rw [← hρu, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hα]
  have e2 : ρv b * algebraMap A Auv (v ^ m) = algebraMap A Auv β := by
    rw [← hρv, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hβ]
  have e3 : algebraMap A Auv (α * v ^ m) = algebraMap A Auv (β * u ^ n) := by
    rw [map_mul, map_mul, ← e1, ← e2, hab]
    ring
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (u * v)) Auv).mp e3
  have huv : (u * v) ^ k ∈ nonZeroDivisors A :=
    _root_.pow_mem (mul_mem H.u_mem H.v_mem) k
  have e4 : α * v ^ m = β * u ^ n := by
    rw [mul_comm ((u * v) ^ k), mul_comm ((u * v) ^ k)] at hk
    exact (mul_cancel_right_mem_nonZeroDivisors huv).mp hk
  have hmem : v ^ m * α ∈ Ideal.span {u ^ n} :=
    Ideal.mem_span_singleton'.mpr ⟨β, by rw [mul_comm (v ^ m), e4]⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (H.mem_of_pow_mul_mem n m α hmem)
  have hun : u ^ n ∈ nonZeroDivisors A := _root_.pow_mem H.u_mem n
  have hβ' : β = c * v ^ m := by
    apply (mul_cancel_right_mem_nonZeroDivisors hun).mp
    linear_combination e4.symm
  refine ⟨c, ?_, ?_⟩
  · have hu : IsUnit (algebraMap A Au (u ^ n)) :=
      IsLocalization.map_units Au (⟨u ^ n, n, rfl⟩ : Submonoid.powers u)
    apply hu.mul_left_injective
    simp only
    rw [hα, map_mul]
  · have hv : IsUnit (algebraMap A Av (v ^ m)) :=
      IsLocalization.map_units Av (⟨v ^ m, m, rfl⟩ : Submonoid.powers v)
    apply hv.mul_left_injective
    simp only
    rw [hβ, hβ', map_mul]

/-- The equalizer data pass to localizations. -/
theorem isLocalization {S : Type*} [CommRing S] [Algebra A S] (M : Submonoid A)
    [IsLocalization M S] : NodeEqualizerData (algebraMap A S u) (algebraMap A S v) := by
  have hnzd : ∀ w ∈ nonZeroDivisors A, algebraMap A S w ∈ nonZeroDivisors S := by
    intro w hw
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    simp only at hx ⊢
    rw [← IsLocalization.mk'_one (M := M) S w, ← IsLocalization.mk'_mul, mul_one,
      IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨c, hc⟩ := hx
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨c, ?_⟩
    apply (mul_cancel_right_mem_nonZeroDivisors hw).mp
    rw [zero_mul, mul_assoc]
    exact hc
  refine ⟨hnzd u H.u_mem, hnzd v H.v_mem, ?_⟩
  intro x hx
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
  obtain ⟨⟨b, n⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  simp only at hy ⊢
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq] at hy
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).mp hy
  have hmem : v * (c * n * a) ∈ Ideal.span {u} :=
    Ideal.mem_span_singleton'.mpr ⟨c * m * b, by linear_combination hc⟩
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (H.sat _ hmem)
  refine Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' S w (c * n * m), ?_⟩
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq, mul_comm u w,
    hw]
  simp only [Submonoid.coe_mul, map_mul]
  ring

end NodeEqualizerData

end Equalizer

section NodeModel

open DeJongAlterations.Algebra.NodeBlowupChart in
/-- The node algebra `R[u,v]/(uv - h)` with `h` a non-zero-divisor satisfies the equalizer
hypotheses for its two coordinates. -/
theorem nodeEqualizerData_node {R : Type u} [CommRing R] {h : R} (hh : h ∈ nonZeroDivisors R) :
    NodeEqualizerData (coordinate h 0) (coordinate h 1) := by
  have hprod : coordinate h 0 * coordinate h 1 = algebraMap R (Node R h) h :=
    DeJongAlterations.Algebra.NodeDomain.nodeCoordinateProduct h
  have hflat : Module.Flat R (Node R h) := DeJongAlterations.Algebra.NodeFamilyFlat.node_flat h
  have hreg : IsSMulRegular (Node R h) (algebraMap R (Node R h) h) := by
    apply IsSMulRegular.of_flat
    intro a b hab
    exact (mul_cancel_left_mem_nonZeroDivisors hh).mp hab
  have hcoord : ∀ i : Fin 2, coordinate h i ∈ nonZeroDivisors (Node R h) := by
    intro i
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have h0 : algebraMap R (Node R h) h • x = algebraMap R (Node R h) h • 0 := by
      rw [smul_eq_mul, smul_zero, ← hprod]
      fin_cases i
      · simp only [Fin.zero_eta] at hx
        linear_combination (coordinate h 1) * hx
      · simp only [Fin.mk_one] at hx
        linear_combination (coordinate h 0) * hx
    exact hreg h0
  refine ⟨hcoord 0, hcoord 1, ?_⟩
  -- the quotient by `u` is `(R/h)[v]`
  let Rh := R ⧸ Ideal.span {h}
  let π₀ : MvPolynomial (Fin 2) R →ₐ[R] Rh[X] := MvPolynomial.aeval ![0, X]
  have hπ₀ : DeJongAlterations.Algebra.NodeChart.uChartIdeal R h ≤ RingHom.ker π₀.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ rfl
    change π₀ (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C h) = 0
    simp only [π₀, map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_sub, neg_eq_zero]
    rw [Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self h), map_zero]
  let π : Node R h →ₐ[R] Rh[X] := Ideal.Quotient.liftₐ _ π₀ (fun a ha => hπ₀ ha)
  let J := Ideal.span {coordinate h 0}
  let ψ₀ : Rh →+* Node R h ⧸ J := Ideal.Quotient.lift (Ideal.span {h})
    ((Ideal.Quotient.mk J).comp (algebraMap R (Node R h))) (by
      intro r hr
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      simp only [RingHom.comp_apply]
      rw [map_mul (algebraMap R (Node R h)), ← hprod, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
  let ψ : Rh[X] →+* Node R h ⧸ J :=
    Polynomial.eval₂RingHom ψ₀ (Ideal.Quotient.mk J (coordinate h 1))
  have hπmk : ∀ p, π (Ideal.Quotient.mk _ p) = π₀ p := fun p => rfl
  have hπu : π (coordinate h 0) = 0 := by
    rw [coordinate, hπmk]
    simp [π₀]
  have hπv : π (coordinate h 1) = X := by
    rw [coordinate, hπmk]
    simp [π₀]
  have hψπ : ψ.comp π.toRingHom = Ideal.Quotient.mk J := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      change ψ (π (Ideal.Quotient.mk _ (MvPolynomial.C r))) = _
      rw [hπmk]
      simp only [π₀, MvPolynomial.aeval_C, Polynomial.algebraMap_apply, ψ,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    · intro i
      change ψ (π (coordinate h i)) = Ideal.Quotient.mk J (coordinate h i)
      fin_cases i
      · simp only [Fin.zero_eta]
        rw [hπu, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)).symm
      · simp only [Fin.mk_one]
        rw [hπv]
        simp [ψ]
  intro x hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
  have hπx : π x = 0 := by
    have := congrArg π hy
    rw [map_mul, map_mul, hπu, hπv, mul_zero] at this
    exact (isRegular_X.left (this.symm.trans (mul_zero X).symm))
  have hmk : Ideal.Quotient.mk J x = 0 := by
    rw [← hψπ]
    change ψ (π x) = 0
    rw [hπx, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmk

end NodeModel

section Kaehler

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra A S]
  [Algebra R S] [IsScalarTower R A S]

omit [Algebra R A] [Algebra R S] [IsScalarTower R A S] in
theorem isUnit_algebraMap_end_of_isLocalization (M : Submonoid A) [IsLocalization M S]
    (m : M) : IsUnit (algebraMap A (Module.End A S) m) := by
  rw [Module.End.isUnit_iff]
  have hm := IsLocalization.map_units S m
  refine ⟨fun x y hxy => ?_, fun y => ⟨hm.unit⁻¹.val * y, ?_⟩⟩
  · change (m : A) • x = (m : A) • y at hxy
    rw [Algebra.smul_def, Algebra.smul_def] at hxy
    exact hm.mul_left_cancel hxy
  · change (m : A) • (hm.unit⁻¹.val * y) = y
    rw [Algebra.smul_def, ← mul_assoc, IsUnit.mul_val_inv, one_mul]

/-- A derivation `A → S` into a localization `S` of `A` extends to a derivation of `S`. -/
def extendDerivation (M : Submonoid A) [IsLocalization M S] (D : Derivation R A S) :
    Derivation R S S :=
  ((IsLocalizedModule.lift M (KaehlerDifferential.map R R A S) D.liftKaehlerDifferential
    (isUnit_algebraMap_end_of_isLocalization M)).extendScalarsOfIsLocalization M S).compDer
    (KaehlerDifferential.D R S)

theorem extendDerivation_algebraMap (M : Submonoid A) [IsLocalization M S]
    (D : Derivation R A S) (a : A) : extendDerivation M D (algebraMap A S a) = D a := by
  change (IsLocalizedModule.lift M (KaehlerDifferential.map R R A S) D.liftKaehlerDifferential
    (isUnit_algebraMap_end_of_isLocalization M))
    (KaehlerDifferential.D R S (algebraMap A S a)) = D a
  rw [← KaehlerDifferential.map_D R R A S, IsLocalizedModule.lift_apply,
    Derivation.liftKaehlerDifferential_comp_D]

omit [Algebra A S] [IsScalarTower R A S] in
/-- If `Ω_{S/R}` is spanned by `ds` and a derivation sends `s` to `1`, then `c ↦ c • ds` is an
isomorphism `S ≅ Ω_{S/R}`. -/
theorem bijective_smul_D_of_span (s : S)
    (hspan : Submodule.span S {KaehlerDifferential.D R S s} = ⊤) (δ : Derivation R S S)
    (hδ : δ s = 1) : Function.Bijective (fun c : S => c • KaehlerDifferential.D R S s) := by
  refine ⟨fun c c' hcc' => ?_, fun ω => ?_⟩
  · have := congrArg δ.liftKaehlerDifferential hcc'
    simp only [map_smul, Derivation.liftKaehlerDifferential_comp_D, hδ, smul_eq_mul,
      mul_one] at this
    exact this
  · have hω : ω ∈ Submodule.span S {KaehlerDifferential.D R S s} := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hω
    exact ⟨c, hc⟩

end Kaehler

section NodeKaehler

open DeJongAlterations.Algebra.NodeBlowupChart

variable {R : Type u} [CommRing R] (h : R) {S : Type*} [CommRing S] [Algebra (Node R h) S]
  [Algebra R S] [IsScalarTower R (Node R h) S]

/-- On a localization `S` of the node algebra in which the coordinate `xᵢ` is a unit, the
`R`-derivation `∂/∂xᵢ` (`∂xᵢ = 1`, `∂xⱼ = -xⱼ/xᵢ` for the other coordinate). -/
def nodeDerivationAux (i : Fin 2) (hu : IsUnit (algebraMap (Node R h) S (coordinate h i))) :
    {D : Derivation R (Node R h) S // D (coordinate h i) = 1} :=
  let c : Fin 2 → S := fun j => algebraMap (Node R h) S (coordinate h j)
  let P := MvPolynomial (Fin 2) R
  let I := DeJongAlterations.Algebra.NodeChart.uChartIdeal R h
  letI : Algebra P S := ((algebraMap (Node R h) S).comp (Ideal.Quotient.mk I)).toAlgebra
  haveI : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq (fun r =>
    IsScalarTower.algebraMap_apply R (Node R h) S r)
  let F : Fin 2 → S := fun j => if j = i then 1 else -(c j * hu.unit⁻¹.val)
  let D₀ : Derivation R P S := MvPolynomial.mkDerivation R F
  have hD₀ : ∀ p ∈ I, D₀ p = 0 := by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [Derivation.leibniz]
    have hf : D₀ (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C h) = 0 := by
      rw [map_sub, Derivation.leibniz, MvPolynomial.mkDerivation_X, MvPolynomial.mkDerivation_X,
        MvPolynomial.derivation_C, sub_zero, Algebra.smul_def, Algebra.smul_def]
      change c 0 * F 1 + c 1 * F 0 = 0
      have hci : c i * hu.unit⁻¹.val = 1 := IsUnit.mul_val_inv hu
      fin_cases i
      · simp only [F, Fin.zero_eta, Fin.isValue, one_ne_zero, ↓reduceIte, mul_one] at hci ⊢
        rw [mul_neg, mul_left_comm, hci, mul_one, neg_add_cancel]
      · simp only [F, Fin.mk_one, Fin.isValue, zero_ne_one, ↓reduceIte, mul_one] at hci ⊢
        rw [mul_neg, mul_left_comm, hci, mul_one, add_neg_cancel]
    have hq : algebraMap P S (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C h) = 0 := by
      change algebraMap (Node R h) S (Ideal.Quotient.mk I _) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        (show _ ∈ I from Ideal.mem_span_singleton_self _), map_zero]
    rw [hf, smul_zero, zero_add, Algebra.smul_def, hq, zero_mul]
  let L : Node R h →ₗ[R] S := (I.restrictScalars R).liftQ D₀.toLinearMap (fun p hp => hD₀ p hp)
  ⟨Derivation.mk' L (by
    intro a b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    change D₀ (p * q) = Ideal.Quotient.mk I p • D₀ q + Ideal.Quotient.mk I q • D₀ p
    rw [Derivation.leibniz, Algebra.smul_def, Algebra.smul_def,
      Algebra.smul_def (Ideal.Quotient.mk I p), Algebra.smul_def (Ideal.Quotient.mk I q)]
    rfl), by
    change D₀ (MvPolynomial.X i) = 1
    rw [MvPolynomial.mkDerivation_X]
    simp [F]⟩

/-- The `R`-derivation `∂/∂xᵢ` of the node algebra with values in a localization in which the
coordinate `xᵢ` is invertible. -/
def nodeDerivation (i : Fin 2) (hu : IsUnit (algebraMap (Node R h) S (coordinate h i))) :
    Derivation R (Node R h) S :=
  (nodeDerivationAux h i hu).1

theorem nodeDerivation_coordinate (i : Fin 2)
    (hu : IsUnit (algebraMap (Node R h) S (coordinate h i))) :
    nodeDerivation h i hu (coordinate h i) = 1 :=
  (nodeDerivationAux h i hu).2

/-- In any `S`-module of differentials, `u dv + v du = 0` (since `uv = h ∈ R`). -/
theorem coordinate_relation :
    algebraMap (Node R h) S (coordinate h 0) •
        KaehlerDifferential.D R S (algebraMap (Node R h) S (coordinate h 1)) +
      algebraMap (Node R h) S (coordinate h 1) •
        KaehlerDifferential.D R S (algebraMap (Node R h) S (coordinate h 0)) = 0 := by
  have hprod : coordinate h 0 * coordinate h 1 = algebraMap R (Node R h) h :=
    DeJongAlterations.Algebra.NodeDomain.nodeCoordinateProduct h
  rw [← Derivation.leibniz, ← map_mul, hprod, ← IsScalarTower.algebraMap_apply,
    Derivation.map_algebraMap]

/-- On a localization of the node algebra in which `xᵢ` is a unit, `Ω_{S/R}` is spanned by
`dxᵢ`. -/
theorem nodeKaehler_span (M : Submonoid (Node R h)) [IsLocalization M S] (i : Fin 2)
    (hu : IsUnit (algebraMap (Node R h) S (coordinate h i))) :
    Submodule.span S {KaehlerDifferential.D R S (algebraMap (Node R h) S (coordinate h i))} =
      ⊤ := by
  set N := Submodule.span S
    {KaehlerDifferential.D R S (algebraMap (Node R h) S (coordinate h i))}
  have hj : ∀ j : Fin 2,
      KaehlerDifferential.D R S (algebraMap (Node R h) S (coordinate h j)) ∈ N := by
    have hrel := coordinate_relation (S := S) h
    intro j
    by_cases hji : j = i
    · subst hji
      exact Submodule.subset_span rfl
    · have hD : algebraMap (Node R h) S (coordinate h i) •
          KaehlerDifferential.D R S (algebraMap (Node R h) S (coordinate h j)) ∈ N := by
        fin_cases i <;> fin_cases j
        · exact absurd rfl hji
        · simp only [Fin.zero_eta, Fin.mk_one] at hrel ⊢
          rw [eq_neg_of_add_eq_zero_left hrel]
          exact N.neg_mem (N.smul_mem _ (Submodule.subset_span rfl))
        · simp only [Fin.zero_eta, Fin.mk_one] at hrel ⊢
          rw [eq_neg_of_add_eq_zero_right hrel]
          exact N.neg_mem (N.smul_mem _ (Submodule.subset_span rfl))
        · exact absurd rfl hji
      have := N.smul_mem hu.unit⁻¹.val hD
      rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  rw [eq_top_iff,
    ← KaehlerDifferential.span_range_map_derivation_of_isLocalization R (Node R h) S M,
    Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  simp only [Function.comp_apply, KaehlerDifferential.map_D]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C r =>
    change KaehlerDifferential.D R S (algebraMap (Node R h) S (algebraMap R (Node R h) r)) ∈ N
    rw [← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap]
    exact N.zero_mem
  | add p q hp hq =>
    rw [map_add, map_add, map_add]
    exact N.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, map_mul, Derivation.leibniz]
    exact N.add_mem (N.smul_mem _ (hj j)) (N.smul_mem _ hp)

/-- **Kähler differentials of the node model.** On a localization `S` of `R[u,v]/(uv - h)` in
which the coordinate `xᵢ` is a unit, `Ω_{S/R}` is free on `dxᵢ`: the map `c ↦ c • dxᵢ` is
bijective (blueprint `lem:sm-omega-node-kaehler`). -/
theorem nodeKaehler_bijective (M : Submonoid (Node R h)) [IsLocalization M S] (i : Fin 2)
    (hu : IsUnit (algebraMap (Node R h) S (coordinate h i))) :
    Function.Bijective (fun c : S =>
      c • KaehlerDifferential.D R S (algebraMap (Node R h) S (coordinate h i))) :=
  bijective_smul_D_of_span _ (nodeKaehler_span h M i hu)
    (extendDerivation M (nodeDerivation h i hu))
    (by rw [extendDerivation_algebraMap, nodeDerivation_coordinate])

end NodeKaehler

end DeJongAlterations.StableModification.Omega
