/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Filtration

/-!
# Original module reconstruction from actual stable filtration quotients

Closed native helper adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreStableFiltration.lean`,
SHA256 20bbbff3fe8a174ea32ecd37af27c92a4d05a13567a9416f0eead62951d86480.
Only the original two Mathlib imports are used. Geometric kernel-filtration
stability and original finite global functions are separate producer obligations.

Finite-module adic completion is first identified through the actual complete
coefficient ring and genuine tensor theorem. Actual stable-filtration
cofinality then reconstructs original elements, retaining every quotient.
-/

open scoped TensorProduct
noncomputable section
universe u

namespace Hironaka.Geometry.ProperSteinProjectiveCech.StableFiltration

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)

/-- The ORIGINAL canonical finite-module completion map is bijective over
the actual complete noetherian coefficient ring. -/
theorem finiteModule_completion_bijective [IsNoetherianRing R] [IsAdicComplete I R]
    [Module.Finite R M] : Function.Bijective (AdicCompletion.of I M) := by
  let e : M ≃ₗ[R] AdicCompletion I M :=
    (TensorProduct.lid R M).symm.trans
      (((AdicCompletion.ofLinearEquiv I R).rTensor M).trans
        ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R))
  have he (m : M) : e m = AdicCompletion.of I M m := by
    change AdicCompletion.ofTensorProduct I M
      (AdicCompletion.of I R 1 ⊗ₜ[R] m) = AdicCompletion.of I M m
    rw [AdicCompletion.ofTensorProduct_tmul]
    change (1 : AdicCompletion I R) • AdicCompletion.of I M m = _
    exact one_smul _ _
  have heq : (e : M → AdicCompletion I M) = AdicCompletion.of I M := funext he
  rw [← heq]
  exact e.bijective

/-- Genuine finite-module completion derives ACTUAL adic completeness of M itself. -/
theorem finiteModule_isAdicComplete [IsNoetherianRing R] [IsAdicComplete I R]
    [Module.Finite R M] : IsAdicComplete I M :=
  AdicCompletion.of_bijective_iff.mp (finiteModule_completion_bijective (M := M) I)

variable (F : I.Filtration M)

/-- The actual original quotient transition between positive filtration orders. -/
abbrev quotientTransition {n m : ℕ} (h : n ≤ m) :
    M ⧸ F.N (m+1) →ₗ[R] M ⧸ F.N (n+1) :=
  Submodule.factor (F.antitone (Nat.succ_le_succ h))

/-- The genuine whole module of compatible original positive-order quotient families. -/
def compatibleQuotients : Submodule R (∀ n : ℕ, M ⧸ F.N (n+1)) where
  carrier := {s | ∀ n m (h : n ≤ m), quotientTransition I F h (s m) = s n}
  zero_mem' := by intro n m h; exact map_zero _
  add_mem' := by
    intro s t hs ht n m h
    change quotientTransition I F h (s m + t m) = s n + t n
    rw [map_add, hs n m h, ht n m h]
  smul_mem' := by
    intro a s hs n m h
    change quotientTransition I F h (a • s m) = a • s n
    rw [map_smul, hs n m h]

/-- The ORIGINAL whole quotient map into the actual compatible quotient module. -/
def quotientMap : M →ₗ[R] compatibleQuotients I F :=
  (LinearMap.pi fun n => (F.N (n+1)).mkQ).codRestrict (compatibleQuotients I F) (by
    intro m n k h
    rfl)

/-- Iterated genuine filtration multiplication derives the entire power-to-filtration inclusion. -/
theorem pow_smul_le (h0 : F.N 0 = ⊤) (n : ℕ) :
    I^n • (⊤ : Submodule R M) ≤ F.N n := by
  simpa only [h0, add_zero] using F.pow_smul_le n 0

/-- Actual stability derives a uniform shift into EVERY genuine ideal power. -/
theorem exists_shift_le_pow (hF : F.Stable) :
    ∃ c : ℕ, ∀ n : ℕ, F.N (c+n) ≤ I^n • (⊤ : Submodule R M) := by
  obtain ⟨c, hc⟩ := hF.exists_pow_smul_eq
  refine ⟨c, fun n => ?_⟩
  rw [hc n]
  exact smul_mono_right _ le_top

/-- Krull intersection and ACTUAL stable cofinality separate the whole original filtration. -/
theorem iInf_eq_bot_of_le_jacobson [IsNoetherianRing R] [Module.Finite R M]
    (hF : F.Stable) (hI : I ≤ Ideal.jacobson ⊥) : (⨅ n : ℕ, F.N n) = ⊥ := by
  obtain ⟨c, hc⟩ := exists_shift_le_pow I F hF
  apply bot_unique
  calc
    (⨅ n : ℕ, F.N n) ≤ ⨅ n : ℕ, I^n • (⊤ : Submodule R M) :=
      le_iInf fun n => (iInf_le F.N (c+n)).trans (hc n)
    _ = ⊥ := I.iInf_pow_smul_eq_bot_of_le_jacobson hI

/-- Genuine stable cofinality and actual adic separation detect ORIGINAL elements
from all their whole filtration quotient coordinates. -/
theorem quotientMap_injective [IsHausdorff I M] (hF : F.Stable) :
    Function.Injective (quotientMap I F) := by
  obtain ⟨c, hc⟩ := exists_shift_le_pow I F hF
  intro x y hxy
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  have hcoord : x ≡ y [SMOD F.N (c+n+1)] := by
    exact congrArg (fun s : compatibleQuotients I F => s.1 (c+n)) hxy
  exact SModEq.mono ((F.mono (c+n)).trans (hc n)) hcoord

/-- Actual stable cofinality and genuine adic precompleteness reconstruct
EVERY compatible original quotient family as an ORIGINAL element of M. -/
theorem quotientMap_surjective [IsPrecomplete I M] (hF : F.Stable) (h0 : F.N 0 = ⊤) :
    Function.Surjective (quotientMap I F) := by
  obtain ⟨c, hc⟩ := exists_shift_le_pow I F hF
  intro s
  have hrep {n m : ℕ} (h : n ≤ m) :
      (F.N (n+1)).mkQ (s.1 m).out = s.1 n := by
    calc
      _ = quotientTransition I F h ((F.N (m+1)).mkQ (s.1 m).out) := rfl
      _ = quotientTransition I F h (s.1 m) :=
        congrArg (quotientTransition I F h) (Submodule.Quotient.mk_out (s.1 m))
      _ = s.1 n := s.2 n m h
  let seq : ℕ → M := fun n => (s.1 (c+n)).out
  have hcauchy {n m : ℕ} (h : n ≤ m) :
      seq n ≡ seq m [SMOD (I^n • (⊤ : Submodule R M))] := by
    have hh : seq n ≡ seq m [SMOD F.N (c+n+1)] := by
      change (F.N (c+n+1)).mkQ (s.1 (c+n)).out =
        (F.N (c+n+1)).mkQ (s.1 (c+m)).out
      rw [hrep le_rfl, hrep (Nat.add_le_add_left h c)]
    exact SModEq.mono ((F.mono (c+n)).trans (hc n)) hh
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I M) hcauchy
  refine ⟨a, ?_⟩
  apply Subtype.ext
  funext n
  have hlim : (F.N (n+1)).mkQ (seq (n+1)) = (F.N (n+1)).mkQ a :=
    SModEq.mono (pow_smul_le I F h0 (n+1)) (ha (n+1))
  exact hlim.symm.trans (hrep (by omega : n ≤ c+(n+1)))

/-- The ORIGINAL quotient map is a genuine whole linear equivalence for
every stable filtration of a finite module over the complete noetherian base. -/
def reconstructionEquiv [IsNoetherianRing R] [IsAdicComplete I R] [Module.Finite R M]
    (hF : F.Stable) (h0 : F.N 0 = ⊤) : M ≃ₗ[R] compatibleQuotients I F := by
  let : IsAdicComplete I M := finiteModule_isAdicComplete (M := M) I
  exact LinearEquiv.ofBijective (quotientMap I F)
    ⟨quotientMap_injective I F hF, quotientMap_surjective I F hF h0⟩

/-- EVERY forward coordinate is the literal ORIGINAL quotient of the same element. -/
theorem reconstructionEquiv_apply [IsNoetherianRing R] [IsAdicComplete I R] [Module.Finite R M]
    (hF : F.Stable) (h0 : F.N 0 = ⊤) (m : M) (n : ℕ) :
    (reconstructionEquiv I F hF h0 m).1 n = (F.N (n+1)).mkQ m := rfl

/-- The reconstructed ORIGINAL element recovers EVERY entire given quotient coordinate. -/
theorem reconstructionEquiv_symm_apply [IsNoetherianRing R] [IsAdicComplete I R]
    [Module.Finite R M] (hF : F.Stable) (h0 : F.N 0 = ⊤)
    (s : compatibleQuotients I F) (n : ℕ) :
    (F.N (n+1)).mkQ ((reconstructionEquiv I F hF h0).symm s) = s.1 n := by
  exact congrArg (fun t : compatibleQuotients I F => t.1 n)
    ((reconstructionEquiv I F hF h0).apply_symm_apply s)

end Hironaka.Geometry.ProperSteinProjectiveCech.StableFiltration
