import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Pivot saturation and pivot-torsion quotients (G10-02-06.d, algebra for 06/09)

Lane G10SB, run 0081.  Hironaka 1975 (4.2.1)–(4.3.1), printed pp. 534–535: the reduced transform is the
pulled module modulo its torsion, and it does not depend on intermediate pull-backs.  At chart level the
torsion is the power torsion of one exceptional generator `h` (the pivot).  This module proves the pure
algebra used to compare such quotients:

* `powerSat K h` — the saturation `{a | ∃ m, hᵐ a ∈ K}` (`le_powerSat`, `powerSat_mono`, `powerSat_powerSat`);
* `powerSat_eq_of_le_of_le_powerSat` — **insensitivity**: `K ≤ K' ≤ powerSat K h → powerSat K' h = powerSat K h`
  (the joint ideal of `Y ×_X X'` and the total transform of the graph have the same strict ideal);
* `powerSat_powerSat_mul` — **composition of two strict transforms**: saturating by `h₁` then by `h₂` is
  saturating by `h₁ h₂` (algebraic core of G10-02-09);
* `ker_mk_powerSat` — the kernel of `A ⧸ K → A ⧸ powerSat K h` is the literal pivot torsion
  `Submodule.torsion' (A ⧸ K) (A ⧸ K) (Submonoid.powers (mk h))` (the form of TN `pivotTorsion`);
* `torsionQuotientEquiv` — `(A ⧸ K) ⧸ pivot torsion ≃+* A ⧸ powerSat K h`.

No analytic input; no named input.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation

noncomputable section

variable {A : Type*} [CommRing A]

/-- The saturation of `K` by the powers of `h`. -/
def powerSat (K : Ideal A) (h : A) : Ideal A where
  carrier := {a | ∃ m : ℕ, h ^ m * a ∈ K}
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨k, hk⟩
    refine ⟨m + k, ?_⟩
    have h1 := K.mul_mem_left (h ^ k) hm
    have h2 := K.mul_mem_left (h ^ m) hk
    have hsum := K.add_mem h1 h2
    have he : h ^ (m + k) * (a + b) = h ^ k * (h ^ m * a) + h ^ m * (h ^ k * b) := by ring
    rw [he]
    exact hsum
  zero_mem' := ⟨0, by rw [mul_zero]; exact K.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have he : h ^ m * (c • a) = c * (h ^ m * a) := by rw [smul_eq_mul]; ring
    rw [he]
    exact K.mul_mem_left c hm

theorem mem_powerSat {K : Ideal A} {h a : A} : a ∈ powerSat K h ↔ ∃ m : ℕ, h ^ m * a ∈ K :=
  Iff.rfl

theorem le_powerSat (K : Ideal A) (h : A) : K ≤ powerSat K h :=
  fun a ha => ⟨0, by rw [pow_zero, one_mul]; exact ha⟩

theorem powerSat_mono {K K' : Ideal A} (hKK' : K ≤ K') (h : A) : powerSat K h ≤ powerSat K' h :=
  fun _ ⟨m, hm⟩ => ⟨m, hKK' hm⟩

theorem powerSat_powerSat (K : Ideal A) (h : A) : powerSat (powerSat K h) h = powerSat K h := by
  refine le_antisymm ?_ (le_powerSat _ h)
  rintro a ⟨m, k, hk⟩
  refine ⟨k + m, ?_⟩
  have he : h ^ (k + m) * a = h ^ k * (h ^ m * a) := by ring
  rw [he]
  exact hk

/-- **Insensitivity of the strict ideal**: any ideal between `K` and its saturation has the same
saturation. -/
theorem powerSat_eq_of_le_of_le_powerSat {K K' : Ideal A} {h : A} (h₁ : K ≤ K')
    (h₂ : K' ≤ powerSat K h) : powerSat K' h = powerSat K h :=
  le_antisymm ((powerSat_mono h₂ h).trans (powerSat_powerSat K h).le) (powerSat_mono h₁ h)

/-- **Two strict transforms compose**: saturating by `h₁` and then by `h₂` is saturating by `h₁ h₂`. -/
theorem powerSat_powerSat_mul (K : Ideal A) (h₁ h₂ : A) :
    powerSat (powerSat K h₁) h₂ = powerSat K (h₁ * h₂) := by
  ext a
  constructor
  · rintro ⟨m, k, hk⟩
    refine ⟨m + k, ?_⟩
    have he : (h₁ * h₂) ^ (m + k) * a = (h₁ ^ m * h₂ ^ k) * (h₁ ^ k * (h₂ ^ m * a)) := by ring
    rw [he]
    exact K.mul_mem_left _ hk
  · rintro ⟨m, hm⟩
    refine ⟨m, m, ?_⟩
    have he : h₁ ^ m * (h₂ ^ m * a) = (h₁ * h₂) ^ m * a := by ring
    rw [he]
    exact hm

/-- An ideal described by the saturation membership law IS the saturation. -/
theorem eq_powerSat_of_forall {K J : Ideal A} {h : A}
    (hJ : ∀ v, v ∈ J ↔ ∃ q : ℕ, h ^ q * v ∈ K) : J = powerSat K h := by
  ext v
  exact hJ v

theorem mul_mem_powerSat_iff (K : Ideal A) (h a : A) :
    h * a ∈ powerSat K h ↔ a ∈ powerSat K h := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    have he : h ^ (m + 1) * a = h ^ m * (h * a) := by ring
    rw [he]
    exact hm
  · exact fun ha => (powerSat K h).mul_mem_left h ha

/-- The pivot is a non-zero-divisor modulo the saturation. -/
theorem isRegular_mk_powerSat (K : Ideal A) (h : A) :
    IsRegular (Ideal.Quotient.mk (powerSat K h) h) := by
  rw [isRegular_iff_eq_zero_of_mul]
  have key : ∀ x : A ⧸ powerSat K h, Ideal.Quotient.mk (powerSat K h) h * x = 0 → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (mul_mem_powerSat_iff K h a).mp hx
  exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩

/-- The pivot torsion of the quotient `A ⧸ K`. -/
abbrev pivotTorsion (K : Ideal A) (h : A) : Ideal (A ⧸ K) :=
  Submodule.torsion' (A ⧸ K) (A ⧸ K) (Submonoid.powers (Ideal.Quotient.mk K h))

theorem mk_mem_pivotTorsion_iff (K : Ideal A) (h a : A) :
    Ideal.Quotient.mk K a ∈ pivotTorsion K h ↔ a ∈ powerSat K h := by
  rw [mem_powerSat]
  constructor
  · rintro ⟨⟨s, hs⟩, hsa⟩
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hs
    refine ⟨m, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
    exact hsa
  · rintro ⟨m, hm⟩
    refine ⟨⟨(Ideal.Quotient.mk K h) ^ m, ⟨m, rfl⟩⟩, ?_⟩
    change (Ideal.Quotient.mk K h) ^ m * Ideal.Quotient.mk K a = 0
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hm

/-- The quotient map from `A ⧸ K` to the strict quotient. -/
def toSat (K : Ideal A) (h : A) : A ⧸ K →+* A ⧸ powerSat K h :=
  Ideal.Quotient.factor (le_powerSat K h)

theorem toSat_surjective (K : Ideal A) (h : A) : Function.Surjective (toSat K h) :=
  Ideal.Quotient.factor_surjective (le_powerSat K h)

/-- The kernel of the strict quotient map is exactly the pivot torsion. -/
theorem ker_toSat (K : Ideal A) (h : A) : RingHom.ker (toSat K h) = pivotTorsion K h := by
  ext s
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [RingHom.mem_ker, mk_mem_pivotTorsion_iff]
  change Ideal.Quotient.mk (powerSat K h) a = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- **The torsion quotient is the strict quotient.** -/
def torsionQuotientEquiv (K : Ideal A) (h : A) :
    (A ⧸ K) ⧸ pivotTorsion K h ≃+* A ⧸ powerSat K h :=
  (Ideal.quotEquivOfEq (ker_toSat K h).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toSat_surjective K h))

theorem torsionQuotientEquiv_mk (K : Ideal A) (h a : A) :
    torsionQuotientEquiv K h (Ideal.Quotient.mk _ (Ideal.Quotient.mk K a)) =
      Ideal.Quotient.mk (powerSat K h) a :=
  rfl

/-- **Reduced transforms do not depend on intermediate pull-backs** (Hironaka (4.3.1)): for
`K ≤ K' ≤ powerSat K h` the two pivot-torsion quotients are isomorphic, compatibly with `A`. -/
def torsionQuotientEquivOfLe {K K' : Ideal A} {h : A} (h₁ : K ≤ K') (h₂ : K' ≤ powerSat K h) :
    (A ⧸ K) ⧸ pivotTorsion K h ≃+* (A ⧸ K') ⧸ pivotTorsion K' h :=
  (torsionQuotientEquiv K h).trans
    ((Ideal.quotEquivOfEq (powerSat_eq_of_le_of_le_powerSat h₁ h₂).symm).trans
      (torsionQuotientEquiv K' h).symm)

theorem torsionQuotientEquivOfLe_mk {K K' : Ideal A} {h : A} (h₁ : K ≤ K')
    (h₂ : K' ≤ powerSat K h) (a : A) :
    torsionQuotientEquivOfLe h₁ h₂ (Ideal.Quotient.mk _ (Ideal.Quotient.mk K a)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk K' a) := by
  apply (torsionQuotientEquiv K' h).injective
  rw [torsionQuotientEquivOfLe, RingEquiv.trans_apply, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply, torsionQuotientEquiv_mk, torsionQuotientEquiv_mk]
  rfl

end

end Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation
