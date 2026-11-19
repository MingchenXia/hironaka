import Hironaka.Analytic.Unibranch.HironakaG10HolomorphicArtinianParameters
import Mathlib.RingTheory.Ideal.Quotient.Operations
set_option autoImplicit false
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue
open Hironaka Hironaka
  HironakaHolomorphicPointJets
open Hironaka.Analytic.Unibranch.HironakaG10HolomorphicArtinianParameters
noncomputable section

local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra

/-- Evaluation at the original base point as a complex-algebra map. -/
def germEvalAlg (n : ℕ) : HolGerm (ComplexModel n) →ₐ[ℂ] ℂ where
  toRingHom := HolGerm.eval
  commutes' c := HolGerm.eval_constHom c

/-- Evaluation descends to every proper actual germ quotient. -/
def quotientResidue (n : ℕ) (J : Ideal (HolGerm (ComplexModel n))) (hJ : J ≠ ⊤) :
    HolGerm (ComplexModel n) ⧸ J →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ J (germEvalAlg n) (fun a ha =>
    (HolGerm.mem_maximalIdeal_iff a).mp ((IsLocalRing.le_maximalIdeal hJ) ha))

@[simp] theorem quotientResidue_mk (n : ℕ) (J : Ideal (HolGerm (ComplexModel n)))
    (hJ : J ≠ ⊤) (a : HolGerm (ComplexModel n)) :
    quotientResidue n J hJ (Ideal.Quotient.mk J a) = HolGerm.eval a := rfl

/-- Its kernel is the actual quotient maximal ideal. -/
theorem quotientResidue_ker (n : ℕ) (J : Ideal (HolGerm (ComplexModel n))) (hJ : J ≠ ⊤) :
    letI : Nontrivial (HolGerm (ComplexModel n) ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    letI : IsLocalRing (HolGerm (ComplexModel n) ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    RingHom.ker (quotientResidue n J hJ).toRingHom =
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n) ⧸ J) := by
  let : Nontrivial (HolGerm (ComplexModel n) ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  let : IsLocalRing (HolGerm (ComplexModel n) ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have heval : RingHom.ker (germEvalAlg n).toRingHom =
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
    ext a
    change HolGerm.eval a = 0 ↔ a ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))
    exact (HolGerm.mem_maximalIdeal_iff a).symm
  have hJker : J ≤ RingHom.ker (germEvalAlg n).toRingHom := by
    intro a ha
    exact (HolGerm.mem_maximalIdeal_iff a).mp ((IsLocalRing.le_maximalIdeal hJ) ha)
  have heq : (quotientResidue n J hJ).toRingHom =
      Ideal.Quotient.lift J (germEvalAlg n).toRingHom hJker := by
    apply RingHom.ext
    intro x
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  calc
    RingHom.ker (quotientResidue n J hJ).toRingHom =
        Ideal.map (Ideal.Quotient.mk J) (RingHom.ker (germEvalAlg n).toRingHom) := by
          rw [heq]
          exact Ideal.ker_quotient_lift (germEvalAlg n).toRingHom hJker
    _ = IsLocalRing.maximalIdeal (HolGerm (ComplexModel n) ⧸ J) := by
      rw [heval]
      exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

/-- The kernel of the canonical residue map on an actual proper point
truncation is nilpotent. -/
theorem truncatedResidue_ker_nilpotent (n q : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (hproper : I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ≠ ⊤) :
    ∃ m : ℕ, RingHom.ker (quotientResidue n
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) hproper).toRingHom ^ m = ⊥ := by
  let J := I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q
  let : Nontrivial (HolGerm (ComplexModel n) ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (HolGerm (ComplexModel n) ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  rw [quotientResidue_ker]
  obtain ⟨hlocal,r,_,m,hm⟩ := truncated_germ_finite_local_nilpotent n q I hproper
  exact ⟨m,hm⟩
end
end Hironaka.Analytic.Unibranch.HironakaG10TruncatedParameterResidue
