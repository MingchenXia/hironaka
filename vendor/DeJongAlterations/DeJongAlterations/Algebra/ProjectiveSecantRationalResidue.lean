import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Etale.Basic

/-!
# The actual residue extension of an original rational algebra point
-/

noncomputable section

namespace DeJongAlterations.Algebra.ProjectiveSecant

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- The original algebra point's actual prime ideal, with its original coefficient map retained. -/
def rationalPointIdeal (e : A →ₐ[k] k) : Ideal A := RingHom.ker e.toRingHom

instance rationalPointIdeal_isPrime (e : A →ₐ[k] k) : (rationalPointIdeal e).IsPrime :=
  (inferInstance : (⊥ : Ideal k).IsPrime).comap e.toRingHom

/-- Original coefficient preservation proves surjectivity internally. -/
theorem rationalPoint_surjective (e : A →ₐ[k] k) : Function.Surjective e :=
  fun a => ⟨algebraMap k A a, e.commutes a⟩

/-- The actual native residue field of the original point is the original coefficient field. -/
def rationalResidueEquiv (e : A →ₐ[k] k) : (rationalPointIdeal e).ResidueField ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ (rationalPointIdeal e) (⊥ : Ideal k) e rfl)
    ((RingHom.surjectiveOnStalks_of_surjective (rationalPoint_surjective e)).residueFieldMap_bijective
      (rationalPointIdeal e) (⊥ : Ideal k) rfl)).trans (Ideal.algEquivResidueFieldOfField (⊥ : Ideal k)).symm

/-- The entire original residue isomorphism retains the literal original coefficient inclusion. -/
@[simp]
theorem rationalResidueEquiv_algebraMap (e : A →ₐ[k] k) (a : k) :
    rationalResidueEquiv e (algebraMap k (rationalPointIdeal e).ResidueField a) = a :=
  (rationalResidueEquiv e).commutes a

/-- Formal etaleness is internally derived for this original rational residue extension over any original field. -/
instance rationalResidue_formallyEtale (e : A →ₐ[k] k) :
    Algebra.FormallyEtale k (rationalPointIdeal e).ResidueField :=
  Algebra.FormallyEtale.of_equiv (rationalResidueEquiv e).symm

end DeJongAlterations.Algebra.ProjectiveSecant
