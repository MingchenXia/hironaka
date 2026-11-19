import Hironaka.Algebra.ProjectiveSecantProjectionUnramified
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Unramified.Locus

/-!
# The actual derivative unit in an actual localization gives original formal unramifiedness

The native square-zero Taylor proof is the same argument as the proved
monogenic helper, followed by actual native localization extensionality.
This is an algebraic helper; the geometric producer must derive its relation
and localized derivative unit from original source and centre data.
-/

noncomputable section

open Polynomial Algebra

namespace Hironaka.Algebra.ProjectiveSecant

/-- An actual original monogenic relation whose derivative becomes a unit in the actual original source localization gives genuine original formal unramifiedness there. -/
theorem formallyUnramified_localization_of_monogenic_relation
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (M : Submonoid S) [IsLocalization M T]
    (t : S) (hgen : Algebra.adjoin R {t} = ⊤) (G : R[X])
    (hG : Polynomial.aeval t G = 0)
    (hG' : IsUnit (Polynomial.aeval (algebraMap S T t) G.derivative)) :
    Algebra.FormallyUnramified R T := by
  let t' := algebraMap S T t
  have hGt : Polynomial.aeval t' G = 0 := by
    change Polynomial.aeval ((Algebra.algHom R S T) t) G = 0
    rw [Polynomial.aeval_algHom_apply, hG, map_zero]
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f₁ f₂ e
  have ht : f₁ t' = f₂ t' := by
    have hd : f₁ t' - f₂ t' ∈ I := by
      simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using AlgHom.congr_fun e t'
    have h := Polynomial.eval_add_of_sq_eq_zero (G.map (algebraMap R B)) (f₂ t')
      (f₁ t' - f₂ t') (show (f₁ t' - f₂ t') ^ 2 ∈ ⊥ from hI ▸ Ideal.pow_mem_pow hd 2)
    simp only [add_sub_cancel, eval_map_algebraMap, aeval_algHom_apply, hGt, map_zero,
      derivative_map, zero_add] at h
    rwa [eq_comm, (hG'.map f₂).mul_right_eq_zero, sub_eq_zero] at h
  have hsurj : Function.Surjective (Polynomial.aeval (R := R) t) :=
    (AlgHom.range_eq_top _).mp ((Algebra.adjoin_singleton_eq_range_aeval R t).symm.trans hgen)
  apply IsLocalization.algHom_ext M
  ext z
  obtain ⟨P, rfl⟩ := hsurj z
  change f₁ (algebraMap S T (Polynomial.aeval t P)) = f₂ (algebraMap S T (Polynomial.aeval t P))
  have hP : algebraMap S T (Polynomial.aeval t P) = Polynomial.aeval t' P := by
    change (Algebra.algHom R S T) (Polynomial.aeval t P) = Polynomial.aeval ((Algebra.algHom R S T) t) P
    rw [Polynomial.aeval_algHom_apply]
  rw [hP, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, ht]

/-- Actual derivative nonmembership in the actual original source prime gives native original unramifiedness at that prime, without local monogenic generation or a unique-prime hypothesis. -/
theorem isUnramifiedAt_of_monogenic_relation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (t : S) (hgen : Algebra.adjoin R {t} = ⊤) (G : R[X])
    (hG : Polynomial.aeval t G = 0) (Q : Ideal S) [Q.IsPrime]
    (hG' : Polynomial.aeval t G.derivative ∉ Q) : Algebra.IsUnramifiedAt R Q := by
  apply formallyUnramified_localization_of_monogenic_relation Q.primeCompl t hgen G hG
  change IsUnit (Polynomial.aeval ((Algebra.algHom R S (Localization.AtPrime Q)) t) G.derivative)
  rw [Polynomial.aeval_algHom_apply]
  exact IsLocalization.map_units (M := Q.primeCompl) (Localization.AtPrime Q) ⟨_, hG'⟩

end Hironaka.Algebra.ProjectiveSecant
