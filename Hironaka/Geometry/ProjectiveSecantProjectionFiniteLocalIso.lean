import Hironaka.Geometry.ProjectiveSecantProjectionLocalBridge
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The native Nakayama theorem applied to actual original finite Spec local data
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original finite Spec geometry internally produces its actual native unique-prime-over condition and literal original away-map bijectivity. -/
theorem exists_awayMap_bijective_of_spec_local_data {R S : CommRingCat.{u}} (β : R ⟶ S)
    (hfin : β.hom.Finite) (hinj : Function.Injective β.hom) (Q : PrimeSpectrum S)
    (hfibre : ∀ Q' : PrimeSpectrum S, Spec.map β Q' = Spec.map β Q → Q' = Q)
    (hfu : ((Spec.map β).stalkMap Q).hom.FormallyUnramified)
    [IsIso ((Spec.map β).residueFieldMap Q)] :
    ∃ r ∉ (PrimeSpectrum.comap β.hom Q).asIdeal,
      ∀ r', r ∣ r' → Function.Bijective (Localization.awayMap β.hom r') := by
  let : Algebra R S := β.hom.toAlgebra
  let : Module.Finite R S := hfin
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  let P : PrimeSpectrum R := PrimeSpectrum.comap β.hom Q
  let : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  let : Algebra (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver P.asIdeal Q.asIdeal
  let : Algebra.IsUnramifiedAt R Q.asIdeal := isUnramifiedAt_of_spec_stalkMap β Q hfu
  have hq : P.asIdeal.primesOver S = {Q.asIdeal} := by
    ext J
    constructor
    · intro hJ
      let : J.IsPrime := hJ.1
      let : J.LiesOver P.asIdeal := hJ.2
      have hP : Spec.map β (⟨J, hJ.1⟩ : PrimeSpectrum S) = Spec.map β Q := by
        apply PrimeSpectrum.ext
        exact (Ideal.LiesOver.over (P := J) (p := P.asIdeal)).symm
      exact congrArg PrimeSpectrum.asIdeal (hfibre ⟨J, hJ.1⟩ hP)
    · intro hJ
      obtain rfl := Set.mem_singleton_iff.mp hJ
      exact ⟨Q.isPrime, inferInstance⟩
  have hres : Function.Surjective (algebraMap P.asIdeal.ResidueField Q.asIdeal.ResidueField) :=
    spec_ideal_residueFieldMap_surjective β Q
  exact Localization.exists_awayMap_bijective_of_residueField_surjective hq hres

end Hironaka.Geometry.ProjectiveSecant
