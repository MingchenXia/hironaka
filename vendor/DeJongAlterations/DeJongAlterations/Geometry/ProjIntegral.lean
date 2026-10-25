import DeJongAlterations.Geometry.AffineBlowup

/-!
# Integral projective spectra and affine blowups

The zero homogeneous prime supplies the actual generic point, while the native
Proj stalk isomorphisms give reducedness. In particular, the blowup of a nonzero
ideal in a domain is an integral scheme, without a finite-generation assumption.
-/

open AlgebraicGeometry TopologicalSpace CategoryTheory

noncomputable section

namespace DeJongAlterations.Geometry.ProjIntegral

universe u

variable {A : Type u} [CommRing A] [instDomain : IsDomain A]
variable {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Every native Proj stalk embeds into a localization of the original domain. -/
theorem isReduced_proj : AlgebraicGeometry.IsReduced (Proj 𝒜) := by
  have (x : Proj 𝒜) : _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) := by
    let p := x.asHomogeneousIdeal.toIdeal
    let : p.IsPrime := x.isPrime
    have : _root_.IsReduced (HomogeneousLocalization.AtPrime 𝒜 p) :=
      isReduced_of_injective
        (algebraMap (HomogeneousLocalization.AtPrime 𝒜 p) (Localization.AtPrime p))
        (HomogeneousLocalization.val_injective _)
    exact isReduced_of_injective (Proj.stalkIso 𝒜 x).hom.hom
      (Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

/-- The zero homogeneous prime is relevant exactly when the irrelevant ideal is nonzero. -/
def zeroPoint (h : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥) : Proj 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := by simpa only [HomogeneousIdeal.toIdeal_bot] using (Ideal.isPrime_bot (α := A))
  not_irrelevant_le := by simpa only [le_bot_iff] using h

omit instDomain in
/-- The zero homogeneous prime specializes to every point of the native projective spectrum. -/
theorem isGenericPoint_of_asHomogeneousIdeal_eq_bot (x : Proj 𝒜)
    (hx : x.asHomogeneousIdeal = ⊥) :
    IsGenericPoint x (Set.univ : Set (Proj 𝒜)) := by
  apply Set.eq_univ_of_forall
  intro y
  apply (ProjectiveSpectrum.le_iff_mem_closure 𝒜 x y).mp
  change x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal
  rw [hx]
  exact bot_le

/-- A graded domain with a nonzero irrelevant ideal has an integral native Proj. -/
theorem isIntegral_proj (h : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥) : IsIntegral (Proj 𝒜) := by
  let : AlgebraicGeometry.IsReduced (Proj 𝒜) := isReduced_proj 𝒜
  let : IrreducibleSpace (Proj 𝒜) :=
    (irreducibleSpace_def _).mpr
      (isGenericPoint_of_asHomogeneousIdeal_eq_bot 𝒜 (zeroPoint 𝒜 h) rfl).isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The native affine blowup of a nonzero ideal in a domain is integral. -/
theorem isIntegral_affineBlowup {R : Type u} [CommRing R] [IsDomain R]
    (I : Ideal R) (hI : I ≠ ⊥) : IsIntegral (affineBlowup I) := by
  apply isIntegral_proj
  intro hirr
  apply hI
  apply le_antisymm ?_ bot_le
  intro a ha
  have hmem := HomogeneousIdeal.mem_irrelevant_of_mem (reesGrading I)
    (show 0 < (1 : ℕ) from Nat.zero_lt_one) (reesDegreeOne_mem I a ha)
  rw [hirr] at hmem
  have hz : reesDegreeOne I a ha = 0 := by
    change reesDegreeOne I a ha ∈ (⊥ : Ideal (reesAlgebra I)) at hmem
    exact hmem
  have hc := congrArg (fun p : reesAlgebra I => (p : Polynomial R).coeff 1) hz
  simpa [reesDegreeOne] using hc

end DeJongAlterations.Geometry.ProjIntegral
