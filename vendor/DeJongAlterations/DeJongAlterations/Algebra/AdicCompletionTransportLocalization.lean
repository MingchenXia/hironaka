import DeJongAlterations.Algebra.AdicCompletionTransport
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Native completion of the actual localization at a maximal ideal -/

noncomputable section

namespace AdicCompletion

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal]
variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p]
  [IsLocalRing S]

/-- The actual finite-level algebra isomorphism induced by localization. -/
def localizationQuotientEquiv (n : ℕ) :
    (R ⧸ (p ^ n • ⊤ : Ideal R)) ≃ₐ[R]
      (S ⧸ (IsLocalRing.maximalIdeal S ^ n • ⊤ : Ideal S)) :=
  (Ideal.quotientEquivAlgOfEq R (by simp : (p ^ n • ⊤ : Ideal R) = p ^ n)).trans
    ((IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n).trans
      (Ideal.quotientEquivAlgOfEq R
        (by simp : (IsLocalRing.maximalIdeal S ^ n • ⊤ : Ideal S) =
          IsLocalRing.maximalIdeal S ^ n)).symm)

@[simp]
theorem localizationQuotientEquiv_mk (n : ℕ) (r : R) :
    localizationQuotientEquiv p S n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R S r) := rfl

/-- The actual localization quotient isomorphisms commute with reduction. -/
theorem transitionMap_localizationQuotientEquiv {m n : ℕ} (hmn : m ≤ n)
    (a : R ⧸ (p ^ n • ⊤ : Ideal R)) :
    transitionMap (IsLocalRing.maximalIdeal S) S hmn (localizationQuotientEquiv p S n a) =
      localizationQuotientEquiv p S m (transitionMap p R hmn a) := by
  induction a using Quotient.inductionOn' with
  | _ a => rfl

/-- Localization at a maximal ideal preserves its actual adic completion. -/
def localizationRingEquiv :
    AdicCompletion p R ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S where
  toFun a :=
    ⟨fun n => localizationQuotientEquiv p S n (a.val n), fun hmn => by
      rw [transitionMap_localizationQuotientEquiv, a.property hmn]⟩
  invFun b :=
    ⟨fun n => (localizationQuotientEquiv p S n).symm (b.val n), fun {m n} hmn => by
      apply (localizationQuotientEquiv p S m).injective
      rw [← transitionMap_localizationQuotientEquiv,
        AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, b.property hmn]⟩
  left_inv a := by
    ext n
    exact (localizationQuotientEquiv p S n).symm_apply_apply (a.val n)
  right_inv b := by
    ext n
    exact (localizationQuotientEquiv p S n).apply_symm_apply (b.val n)
  map_mul' a b := by
    ext n
    exact map_mul (localizationQuotientEquiv p S n) (a.val n) (b.val n)
  map_add' a b := by
    ext n
    exact map_add (localizationQuotientEquiv p S n) (a.val n) (b.val n)

@[simp]
theorem localizationRingEquiv_of (a : R) :
    localizationRingEquiv p S (AdicCompletion.of p R a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap R S a) := by
  ext n
  exact localizationQuotientEquiv_mk p S n a

/-- The localization-completion isomorphism preserves the actual coefficient algebra. -/
def localizationAlgEquiv :
    AdicCompletion p R ≃ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal S) S :=
  AlgEquiv.ofRingEquiv (f := localizationRingEquiv p S) fun r => by
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    exact localizationRingEquiv_of p S r

@[simp]
theorem localizationAlgEquiv_of (a : R) :
    localizationAlgEquiv p S (AdicCompletion.of p R a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal S) S (algebraMap R S a) :=
  localizationRingEquiv_of p S a

end AdicCompletion
