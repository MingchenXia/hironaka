/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentrePrincipalParts
import Hironaka.Resolution.HironakaRelativeNormalMonomialBasis
import Mathlib.RingTheory.LocalRing.Module

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentrePrincipalPartsFree
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCentreJointJets HironakaActualCentrePrincipalParts
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames
  HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations

/-- A fixed genuine finite distinct-monomial basis of the TRUE original whole joint word-jet image. -/
def actualJointJetMonomialEquiv (d n q : ℕ) :
    letI := tangentAlgebra d n
    letI := normalExponentFintype n q
    (normalExponentIndex n q → HolGerm (ComplexModel d)) ≃ₗ[HolGerm (ComplexModel d)]
      LinearMap.range (actualJointScalarJet d n q) :=
  letI := tangentAlgebra d n
  letI := normalExponentFintype n q
  (normalPowerLinearEquiv d n q).trans
    ((Submodule.quotEquivOfEq _ _ (ker_actualJointScalarJet d n q).symm).trans
      (actualJointScalarJet d n q).quotKerEquivRange)

/-- Actual finite distinct-monomial representatives in the ENTIRE original joint germ ring. -/
def actualJointMonomialRepresentative (d n q : ℕ) :
    letI := tangentAlgebra d n
    letI := normalExponentFintype n q
    (normalExponentIndex n q → HolGerm (ComplexModel d)) →ₗ[HolGerm (ComplexModel d)]
      HolGerm (ComplexModel (d+n)) :=
  letI := tangentAlgebra d n
  letI := normalExponentFintype n q
  Fintype.linearCombination (HolGerm (ComplexModel d)) (fun α => normalExponentMonomial d n α.val)

/-- Every original monomial representative has precisely its fixed TRUE joint-jet coordinates. -/
theorem actualJointJetMonomialEquiv_representative (d n q : ℕ)
    (a : normalExponentIndex n q → HolGerm (ComplexModel d)) :
    let := tangentAlgebra d n
    let := normalExponentFintype n q
    (actualJointJetMonomialEquiv d n q a).val=
      actualJointScalarJet d n q (actualJointMonomialRepresentative d n q a) := by
  let := tangentAlgebra d n
  let := normalExponentFintype n q
  have hq : normalPowerLinearEquiv d n q a=
      Ideal.Quotient.mk (normalIdeal d n ^ q) (actualJointMonomialRepresentative d n q a) := by
    change Fintype.linearCombination (HolGerm (ComplexModel d))
      (fun α : normalExponentIndex n q => Ideal.Quotient.mk (normalIdeal d n ^ q) (normalExponentMonomial d n α.val)) a=_
    simp only [actualJointMonomialRepresentative,Fintype.linearCombination_apply,map_sum]
    apply Finset.sum_congr rfl
    intro α _
    exact ((Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d n ^ q)).toLinearMap.map_smul
      (a α) (normalExponentMonomial d n α.val)).symm
  change ((actualJointScalarJet d n q).quotKerEquivRange
    ((Submodule.quotEquivOfEq _ _ (ker_actualJointScalarJet d n q).symm)
      (normalPowerLinearEquiv d n q a))).val=_
  rw [hq]
  rfl

/-- Fixed whole ORIGINAL B-linear representative, defined on the TRUE joint word-jet image only. -/
def actualJointJetRepresentative (d n q : ℕ) :
    letI := tangentAlgebra d n
    LinearMap.range (actualJointScalarJet d n q) →ₗ[HolGerm (ComplexModel d)]
      HolGerm (ComplexModel (d+n)) :=
  letI := tangentAlgebra d n
  letI := normalExponentFintype n q
  (actualJointMonomialRepresentative d n q).comp (actualJointJetMonomialEquiv d n q).symm.toLinearMap

/-- The section is an ENTIRE original jet identity, not just a pointwise representative identity. -/
theorem actualJointScalarJet_representative (d n q : ℕ) :
    let := tangentAlgebra d n
    ∀ v : LinearMap.range (actualJointScalarJet d n q),
    actualJointScalarJet d n q (actualJointJetRepresentative d n q v)=v.val := by
  let := tangentAlgebra d n
  let := normalExponentFintype n q
  dsimp only
  intro v
  change actualJointScalarJet d n q
    (actualJointMonomialRepresentative d n q ((actualJointJetMonomialEquiv d n q).symm v))=v.val
  rw [← actualJointJetMonomialEquiv_representative]
  exact congrArg Subtype.val ((actualJointJetMonomialEquiv d n q).apply_symm_apply v)

/-- The TRUE whole joint-jet image is finite over the ORIGINAL tangent germ ring. -/
theorem actualJointJetImage_finite (d n q : ℕ) :
    let := tangentAlgebra d n
    Module.Finite (HolGerm (ComplexModel d)) (LinearMap.range (actualJointScalarJet d n q)) := by
  let := tangentAlgebra d n
  let := normalExponentFintype n q
  exact Module.Finite.equiv (actualJointJetMonomialEquiv d n q)

/-- Distinct original monomials give freeness of the TRUE image, without erasing redundant word relations. -/
theorem actualJointJetImage_free (d n q : ℕ) :
    let := tangentAlgebra d n
    Module.Free (HolGerm (ComplexModel d)) (LinearMap.range (actualJointScalarJet d n q)) := by
  let := tangentAlgebra d n
  let := normalExponentFintype n q
  exact Module.Free.of_equiv (actualJointJetMonomialEquiv d n q)

/-- Restriction of the SAME genuine whole germ projection from TRUE joint image onto the SAME existing row-kernel model. -/
def actualCentreModelRetraction (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U) (hH0 : ∀ i,HolAt (H i) 0)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    letI := tangentAlgebra d (d+t)
    LinearMap.range (actualJointScalarJet d (d+t) q) →ₗ[HolGerm (ComplexModel d)]
      actualCentrePrincipalPartsModel d t q rows :=
  letI := tangentAlgebra d (d+t)
  ((actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet).comp
    (LinearMap.range (actualJointScalarJet d (d+t) q)).subtype).codRestrict _
      (fun v => actualCentreGermProjection_mem_model d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank v.val v.2)

/-- The whole row-kernel model is a TRUE direct summand of the finite free ACTUAL jet image. -/
theorem actualCentreModelRetraction_splits (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U) (hH0 : ∀ i,HolAt (H i) 0)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    let := tangentAlgebra d (d+t)
    (actualCentreModelRetraction d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank).comp
      (Submodule.inclusion (show actualCentrePrincipalPartsModel d t q rows ≤
        LinearMap.range (actualJointScalarJet d (d+t) q) from inf_le_left))=LinearMap.id := by
  let := tangentAlgebra d (d+t)
  dsimp only
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change actualCentreGermProjection d t q H hU hH hD h0D hDU rows cols hdet v.val=v.val
  exact actualCentreGermProjection_fixes_row_kernel d t q H hU hH hD h0D hDU rows cols hdet v.val
    (fun j => congrFun (LinearMap.mem_ker.mp v.2.2) j)

/-- The TRUE existing principal-parts model is finite projective, then free over the ORIGINAL local tangent germ ring. -/
theorem actualCentrePrincipalPartsModel_finite_free (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U) (hH0 : ∀ i,HolAt (H i) 0)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    let := tangentAlgebra d (d+t)
    Module.Finite (HolGerm (ComplexModel d)) (actualCentrePrincipalPartsModel d t q rows) ∧
    Module.Projective (HolGerm (ComplexModel d)) (actualCentrePrincipalPartsModel d t q rows) ∧
    Module.Free (HolGerm (ComplexModel d)) (actualCentrePrincipalPartsModel d t q rows) := by
  let := tangentAlgebra d (d+t)
  dsimp only
  let S := LinearMap.range (actualJointScalarJet d (d+t) q)
  let i : actualCentrePrincipalPartsModel d t q rows →ₗ[HolGerm (ComplexModel d)] S :=
    Submodule.inclusion (show actualCentrePrincipalPartsModel d t q rows ≤ S from inf_le_left)
  let r := actualCentreModelRetraction d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank
  have hs : r.comp i=LinearMap.id := actualCentreModelRetraction_splits d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank
  have hsurj : Function.Surjective r := fun v => ⟨i v,LinearMap.congr_fun hs v⟩
  let : Module.Finite (HolGerm (ComplexModel d)) S := actualJointJetImage_finite d (d+t) q
  let : Module.Free (HolGerm (ComplexModel d)) S := actualJointJetImage_free d (d+t) q
  let : Module.Projective (HolGerm (ComplexModel d)) (actualCentrePrincipalPartsModel d t q rows) :=
    Module.Projective.of_split i r hs
  let : Module.Finite (HolGerm (ComplexModel d)) (actualCentrePrincipalPartsModel d t q rows) :=
    Module.Finite.of_surjective r hsurj
  exact ⟨inferInstance,inferInstance,Module.free_of_flat_of_isLocalRing⟩

/-- Finiteness, projectivity and local freeness of the ENTIRE ORIGINAL quotient, with its genuine original B-action. -/
theorem actualCentrePrincipalPartsQuotient_finite_free (d t q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel (d+t) → ℂ) {U D : Set (ComplexModel (d+t))}
    (hU : IsOpen U) (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hD : IsOpen D)
    (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U) (hH0 : ∀ i,HolAt (H i) 0)
    {k : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k) :
    let := tangentAlgebra d (d+t)
    Module.Finite (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ q)) ∧
    Module.Projective (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ q)) ∧
    Module.Free (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ q)) := by
  let := tangentAlgebra d (d+t)
  dsimp only
  obtain ⟨hf,hp,he⟩ := actualCentrePrincipalPartsModel_finite_free d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank
  let : Module.Finite (HolGerm (ComplexModel d)) (actualCentrePrincipalPartsModel d t q rows) := hf
  let : Module.Projective (HolGerm (ComplexModel d)) (actualCentrePrincipalPartsModel d t q rows) := hp
  let : Module.Free (HolGerm (ComplexModel d)) (actualCentrePrincipalPartsModel d t q rows) := he
  let E := actualCentrePrincipalPartsFrame d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank
  exact ⟨Module.Finite.equiv E.symm,Module.Projective.of_equiv E.symm,Module.Free.of_equiv E.symm⟩

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original coherence, actual regular centre and ALL intrinsic HS constancy give SAME whole original principal parts finite free at EVERY order. -/
theorem exists_original_hs_constant_centre_all_order_principal_parts_free
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C,∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ (O : Set M), IsOpen O ∧ x ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
        (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (G i) O) ∧
        (∀ y ∈ O,∀ g,A.mem y g ↔ IsInSpanAt (n := d+t) (· ∈ range G) y g) ∧
      ∃ (U : Set (ComplexModel (d+t))), ∃ hU : IsOpen U,∃ h0U : (0 : ComplexModel (d+t)) ∈ U,∃ _hUT : U ⊆ Φ.target,
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        ∃ hH : ∀ i,DifferentiableOn ℂ (H i) U,
        ∃ hhol : ∀ p ∈ U,∀ i,HolAt (H i) p,
          (∀ p (hp : p ∈ U),originalCoherentOriginIdeal
            (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p)=translatedIdeal H p (hhol p hp)) ∧
          (∀ p (_hp : p ∈ U) (ℓ : ℕ),
            hilbertSamuelAt A (actualFlatteningInverseMap x Φ p) ℓ=
              Module.finrank ℂ (LinearMap.range (finiteJet (n := d+t) (ℓ+1)))-
                Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))) ∧
          (∀ p ∈ U,p ∈ complexCoordinatePlane (d+t) d → ∀ ℓ : ℕ,
            Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=
              Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H 0))) ∧
          ∃ hH0 : ∀ i,HolAt (H i) 0,
          ∀ ℓ : ℕ,∃ (k : ℕ) (rows : Fin k → monomialIndex (d+t) (ℓ+1))
            (cols : Fin k → monomialIndex (d+t) (ℓ+1) × Fin N),
            k=Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H 0)) ∧
            ∃ D : Set (ComplexModel (d+t)),∃ hD : IsOpen D,∃ h0D : (0 : ComplexModel (d+t)) ∈ D,
            ∃ hDU : D ⊆ U,
              IsOpen ((tangentInclusion d t) ⁻¹' D) ∧ (0 : ComplexModel d) ∈ (tangentInclusion d t) ⁻¹' D ∧
            ∃ hdet : ∀ p ∈ D,(pivotMatrix (ℓ+1) H rows cols p).det ≠ 0,
            ∃ hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
              Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=k,
              IsUnit ((actualCentreMacaulayGerm d t (ℓ+1) H hU hH h0U).submatrix rows cols).det ∧
              letI := tangentAlgebra d (d+t)
              LinearMap.ker (actualCentrePrincipalPartsCoordinates d t (ℓ+1) H hU hH hD h0D hDU hH0 rows cols hdet hrank)=
                (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (ℓ+1)).restrictScalars (HolGerm (ComplexModel d)) ∧
              Function.Surjective (actualCentrePrincipalPartsCoordinates d t (ℓ+1) H hU hH hD h0D hDU hH0 rows cols hdet hrank) ∧
              Nonempty ((HolGerm (ComplexModel (d+(d+t))) ⧸
                  (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (ℓ+1)))
                ≃ₗ[HolGerm (ComplexModel d)] actualCentrePrincipalPartsModel d t (ℓ+1) rows) ∧
              Module.Finite (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t))) ⧸ (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (ℓ+1))) ∧
              Module.Projective (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t))) ⧸ (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (ℓ+1))) ∧
              Module.Free (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t))) ⧸ (actualCentreJointIdeal d t H hH0 ⊔ normalIdeal d (d+t) ^ (ℓ+1))) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hHS,hR,hH0,hpiv⟩ :=
    exists_original_hs_constant_centre_whole_principal_parts C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hHS,hR,hH0,?_⟩
  intro ℓ
  obtain ⟨k,rows,cols,hk,D,hD,h0D,hDU,hV,h0V,hdet,hrank,hunit,hker,hsurj,hframe⟩ := hpiv ℓ
  refine ⟨k,rows,cols,hk,D,hD,h0D,hDU,hV,h0V,hdet,hrank,hunit,?_⟩
  let := tangentAlgebra d (d+t)
  exact ⟨hker,hsurj,hframe,
    actualCentrePrincipalPartsQuotient_finite_free d t (ℓ+1) H hU hH hD h0D hDU hH0 rows cols hdet hrank⟩

end OriginalCentre

end
end Hironaka.HironakaActualCentrePrincipalPartsFree
