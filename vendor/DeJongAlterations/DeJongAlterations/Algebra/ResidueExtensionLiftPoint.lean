import DeJongAlterations.Algebra.ResidueExtensionLift

/-! # The actual unique lifted closed point and its specified residue extension -/

noncomputable section

open Polynomial Algebra TensorProduct

namespace DeJongAlterations.Algebra.ResidueExtensionLift

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] (P : Ideal R) [P.IsMaximal]
  (L : Type u) [Field L] [Algebra P.ResidueField L]
  [FiniteDimensional P.ResidueField L] [Algebra.IsSeparable P.ResidueField L]

/-- The actual lifted prime is the kernel of the constructed specialization to the specified field. -/
def liftPrime : Ideal (LiftRing P L) := RingHom.ker (specialization P L)

instance liftPrime_isMaximal : (liftPrime P L).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (specialization P L) (specialization_surjective P L)

/-- Its actual coefficient contraction is the original closed-point ideal. -/
theorem liftPrime_comap : (liftPrime P L).comap (algebraMap R (LiftRing P L)) = P := by
  ext r
  change specialization P L (algebraMap R (LiftRing P L) r) = 0 ↔ r ∈ P
  rw [specialization_algebraMap]
  constructor
  · intro h
    apply Ideal.algebraMap_residueField_eq_zero.mp
    apply (algebraMap P.ResidueField L).injective
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.algebraMap_residueField_eq_zero.mpr h, map_zero]

/-- The actual unique lifted closed point in the native spectrum. -/
def liftPoint : PrimeSpectrum (LiftRing P L) := ⟨liftPrime P L, inferInstance⟩

theorem liftPoint_map : PrimeSpectrum.comap (algebraMap R (LiftRing P L)) (liftPoint P L) =
    ⟨P, inferInstance⟩ := PrimeSpectrum.ext (liftPrime_comap P L)

/-- The full native fibre, rather than only a selected component, consists of this one point. -/
theorem unique_point_over (q : PrimeSpectrum (LiftRing P L))
    (hq : PrimeSpectrum.comap (algebraMap R (LiftRing P L)) q = ⟨P, inferInstance⟩) :
    q = liftPoint P L := by
  let e := PrimeSpectrum.preimageEquivFiber R (LiftRing P L) ⟨P, inferInstance⟩
  let e' := PrimeSpectrum.homeomorphOfRingEquiv (fibreEquiv P L).toRingEquiv
  have he : e ⟨q, hq⟩ = e ⟨liftPoint P L, liftPoint_map P L⟩ :=
    e'.injective (Subsingleton.elim _ _)
  exact congrArg Subtype.val (e.injective he)

/-- The actual lifted point avoids the source derivative-zero locus. -/
theorem derivative_not_mem_liftPrime : derivativeElement P L ∉ liftPrime P L :=
  specialization_derivative_ne_zero P L

/-- The actual specialization induces the canonical native residue map to the specified field. -/
def residueLift : (liftPrime P L).ResidueField →+* L :=
  Ideal.ResidueField.lift (liftPrime P L) (specialization P L) le_rfl (by
    intro s hs
    exact isUnit_iff_ne_zero.mpr hs)

@[simp]
theorem residueLift_algebraMap (s : LiftRing P L) :
    residueLift P L (algebraMap (LiftRing P L) (liftPrime P L).ResidueField s) =
      specialization P L s := Ideal.ResidueField.lift_algebraMap _ _ _ _ _

theorem residueLift_surjective : Function.Surjective (residueLift P L) := by
  intro y
  obtain ⟨s, hs⟩ := specialization_surjective P L y
  exact ⟨algebraMap (LiftRing P L) (liftPrime P L).ResidueField s,
    (residueLift_algebraMap P L s).trans hs⟩

/-- The actual native residue field at the unique point is the specified extension. -/
def residueFieldEquiv : (liftPrime P L).ResidueField ≃+* L :=
  RingEquiv.ofBijective (residueLift P L)
    ⟨(residueLift P L).injective, residueLift_surjective P L⟩

/-- The actual coefficient-induced map of ideal residue fields. -/
def residueBaseMap : P.ResidueField →+* (liftPrime P L).ResidueField :=
  Ideal.ResidueField.map P (liftPrime P L) (algebraMap R (LiftRing P L))
    (liftPrime_comap P L).symm

/-- The field comparison preserves exactly the originally specified residue extension embedding. -/
theorem residueFieldEquiv_comp :
    (residueFieldEquiv P L).toRingHom.comp (residueBaseMap P L) =
      algebraMap P.ResidueField L := by
  apply Ideal.ResidueField.ringHom_ext
  ext r
  change residueLift P L (residueBaseMap P L (algebraMap R P.ResidueField r)) = _
  rw [residueBaseMap, Ideal.ResidueField.map_algebraMap, residueLift_algebraMap,
    specialization_algebraMap]
  rfl

end DeJongAlterations.Algebra.ResidueExtensionLift
