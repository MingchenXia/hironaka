/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentrePrincipalPartsFree

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentrePrincipalPartsOrderSystem
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualCentrePrincipalParts HironakaActualCentrePrincipalPartsFree
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicPointJets
  HironakaHolomorphicJetChartInvariance HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations

/-- Literal whole original quotient factor map for SAME J and genuine normal powers, with unchanged original B-action. -/
def actualPrincipalPartsTruncation (d n q r : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) (hqr : q ≤ r) :
    letI := tangentAlgebra d n
    (HolGerm (ComplexModel (d+n)) ⧸ (J ⊔ normalIdeal d n ^ r)) →ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+n)) ⧸ (J ⊔ normalIdeal d n ^ q)) :=
  letI := tangentAlgebra d n
  (Ideal.Quotient.factorₐ (HolGerm (ComplexModel d))
    (show J ⊔ normalIdeal d n ^ r ≤ J ⊔ normalIdeal d n ^ q from
      sup_le_sup_left (Ideal.pow_le_pow_right hqr) J)).toLinearMap

/-- EVERY original numerator retains its SAME whole original lower quotient class. -/
theorem actualPrincipalPartsTruncation_mk (d n q r : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) (hqr : q ≤ r)
    (g : HolGerm (ComplexModel (d+n))) :
    let := tangentAlgebra d n
    actualPrincipalPartsTruncation d n q r J hqr (Ideal.Quotient.mk (J ⊔ normalIdeal d n ^ r) g)=
      Ideal.Quotient.mk (J ⊔ normalIdeal d n ^ q) g := by
  let := tangentAlgebra d n
  rfl

/-- The ORIGINAL entire quotient map is surjective, not just a map on chosen finite generators. -/
theorem actualPrincipalPartsTruncation_surjective (d n q r : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) (hqr : q ≤ r) :
    let := tangentAlgebra d n
    Function.Surjective (actualPrincipalPartsTruncation d n q r J hqr) := by
  let := tangentAlgebra d n
  dsimp only
  intro v
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective v
  exact ⟨Ideal.Quotient.mk (J ⊔ normalIdeal d n ^ r) g,rfl⟩

/-- Identity on the ENTIRE original principal-parts module. -/
theorem actualPrincipalPartsTruncation_refl (d n q : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) :
    let := tangentAlgebra d n
    actualPrincipalPartsTruncation d n q q J le_rfl=LinearMap.id := by
  let := tangentAlgebra d n
  dsimp only
  apply LinearMap.ext
  intro v
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective v
  rfl

/-- Exact triple-order cocycle on the ENTIRE upper original quotient, independent of all choices. -/
theorem actualPrincipalPartsTruncation_comp (d n q r s : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) (hqr : q ≤ r) (hrs : r ≤ s) :
    let := tangentAlgebra d n
    (actualPrincipalPartsTruncation d n q r J hqr).comp
      (actualPrincipalPartsTruncation d n r s J hrs)=
        actualPrincipalPartsTruncation d n q s J (hqr.trans hrs) := by
  let := tangentAlgebra d n
  dsimp only
  apply LinearMap.ext
  intro v
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective v
  rfl

/-- Ordinary whole-module algebra: an actual surjection onto a projective target has a linear split and full kernel finite projective/localfree. -/
private theorem exists_split_finite_free_kernel {B M N : Type*} [CommRing B] [IsLocalRing B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] [Module.Projective B M]
    [AddCommGroup N] [Module B N] [Module.Projective B N]
    (f : M →ₗ[B] N) (hf : Function.Surjective f) :
    ∃ s : N →ₗ[B] M,f.comp s=LinearMap.id ∧
      Module.Finite B (LinearMap.ker f) ∧ Module.Projective B (LinearMap.ker f) ∧
        Module.Free B (LinearMap.ker f) := by
  obtain ⟨s,hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  let p : M →ₗ[B] M := LinearMap.id-s.comp f
  have hp : ∀ x,p x ∈ LinearMap.ker f := by
    intro x
    change f (x-s (f x))=0
    rw [map_sub]
    change f x-(f.comp s) (f x)=0
    rw [hs]
    exact sub_self _
  let k : M →ₗ[B] LinearMap.ker f := p.codRestrict _ hp
  have hk : k.comp (LinearMap.ker f).subtype=LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change v.val-s (f v.val)=v.val
    rw [LinearMap.mem_ker.mp v.2,map_zero,sub_zero]
  let : Module.Projective B (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype k hk
  let : Module.Finite B (LinearMap.ker f) :=
    Module.Finite.of_surjective k (fun v => ⟨v.val,LinearMap.congr_fun hk v⟩)
  exact ⟨s,hs,inferInstance,inferInstance,Module.free_of_flat_of_isLocalRing⟩

/-- SAME genuine original family and actual two-order pivot data internally produce a whole B-linear split and finite free ENTIRE kernel. -/
theorem exists_actualPrincipalPartsTruncation_split_kernel (d t q r : ℕ) (hqr : q ≤ r)
    {ι : Type*} [Fintype ι] (H : ι → ComplexModel (d+t) → ℂ)
    {U D E : Set (ComplexModel (d+t))} (hU : IsOpen U)
    (hH : ∀ i,DifferentiableOn ℂ (H i) U) (hH0 : ∀ i,HolAt (H i) 0)
    (hD : IsOpen D) (h0D : (0 : ComplexModel (d+t)) ∈ D) (hDU : D ⊆ U)
    (hE : IsOpen E) (h0E : (0 : ComplexModel (d+t)) ∈ E) (hEU : E ⊆ U)
    {k l : ℕ} (rows : Fin k → monomialIndex (d+t) q) (cols : Fin k → monomialIndex (d+t) q × ι)
    (hdet : ∀ p ∈ D,(pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k)
    (rows' : Fin l → monomialIndex (d+t) r) (cols' : Fin l → monomialIndex (d+t) r × ι)
    (hdet' : ∀ p ∈ E,(pivotMatrix r H rows' cols' p).det ≠ 0)
    (hrank' : ∀ p ∈ E,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap r H p))=l) :
    let := tangentAlgebra d (d+t)
    let J := actualCentreJointIdeal d t H hH0
    ∃ s : (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ q)) →ₗ[HolGerm (ComplexModel d)]
        (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ r)),
      (actualPrincipalPartsTruncation d (d+t) q r J hqr).comp s=LinearMap.id ∧
      Module.Finite (HolGerm (ComplexModel d)) (LinearMap.ker (actualPrincipalPartsTruncation d (d+t) q r J hqr)) ∧
      Module.Projective (HolGerm (ComplexModel d)) (LinearMap.ker (actualPrincipalPartsTruncation d (d+t) q r J hqr)) ∧
      Module.Free (HolGerm (ComplexModel d)) (LinearMap.ker (actualPrincipalPartsTruncation d (d+t) q r J hqr)) := by
  let := tangentAlgebra d (d+t)
  let J := actualCentreJointIdeal d t H hH0
  dsimp only
  have hq := actualCentrePrincipalPartsQuotient_finite_free d t q H hU hH hD h0D hDU hH0 rows cols hdet hrank
  have hr := actualCentrePrincipalPartsQuotient_finite_free d t r H hU hH hE h0E hEU hH0 rows' cols' hdet' hrank'
  let : Module.Projective (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ q)) := hq.2.1
  let : Module.Finite (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ r)) := hr.1
  let : Module.Projective (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ r)) := hr.2.1
  exact exists_split_finite_free_kernel (actualPrincipalPartsTruncation d (d+t) q r J hqr)
    (actualPrincipalPartsTruncation_surjective d (d+t) q r J hqr)

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original source geometry gives ONE genuine family before ALLorders and whole B-linear split truncations with finite free ENTIRE kernels. -/
theorem exists_original_hs_constant_centre_whole_split_order_system
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
      ∃ (U : Set (ComplexModel (d+t))), ∃ _hU : IsOpen U,∃ _h0U : (0 : ComplexModel (d+t)) ∈ U,∃ _hUT : U ⊆ Φ.target,
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        ∃ _hH : ∀ i,DifferentiableOn ℂ (H i) U,
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
          let := tangentAlgebra d (d+t)
          let J := actualCentreJointIdeal d t H hH0
          (∀ ℓ : ℕ,Module.Finite (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (ℓ+1))) ∧
            Module.Projective (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (ℓ+1))) ∧
            Module.Free (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (ℓ+1)))) ∧
          ∀ (ℓ m : ℕ) (hℓm : ℓ ≤ m),∃ s : (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (ℓ+1))) →ₗ[HolGerm (ComplexModel d)]
              (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (m+1))),
            (actualPrincipalPartsTruncation d (d+t) (ℓ+1) (m+1) J (Nat.succ_le_succ hℓm)).comp s=LinearMap.id ∧
            Module.Finite (HolGerm (ComplexModel d)) (LinearMap.ker (actualPrincipalPartsTruncation d (d+t) (ℓ+1) (m+1) J (Nat.succ_le_succ hℓm))) ∧
            Module.Projective (HolGerm (ComplexModel d)) (LinearMap.ker (actualPrincipalPartsTruncation d (d+t) (ℓ+1) (m+1) J (Nat.succ_le_succ hℓm))) ∧
            Module.Free (HolGerm (ComplexModel d)) (LinearMap.ker (actualPrincipalPartsTruncation d (d+t) (ℓ+1) (m+1) J (Nat.succ_le_succ hℓm))) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hHS,hR,hH0,hpiv⟩ :=
    exists_original_hs_constant_centre_all_order_principal_parts_free C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hHS,hR,hH0,?_⟩
  let := tangentAlgebra d (d+t)
  dsimp only
  let J := actualCentreJointIdeal d t H hH0
  have hfree : ∀ ℓ : ℕ,Module.Finite (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (ℓ+1))) ∧
      Module.Projective (HolGerm (ComplexModel d))
        (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (ℓ+1))) ∧
      Module.Free (HolGerm (ComplexModel d))
        (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (ℓ+1))) := by
    intro ℓ
    obtain ⟨k,rows,cols,_hk,D,hD,h0D,hDU,_hV,_h0V,hdet,hrank,_hunit,_hker,_hsurj,_hframe,hfin,hproj,hfree⟩ := hpiv ℓ
    exact ⟨hfin,hproj,hfree⟩
  refine ⟨hfree,?_⟩
  intro ℓ m hℓm
  let : Module.Projective (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (ℓ+1))) := (hfree ℓ).2.1
  let : Module.Finite (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (m+1))) := (hfree m).1
  let : Module.Projective (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (m+1))) := (hfree m).2.1
  exact exists_split_finite_free_kernel
    (actualPrincipalPartsTruncation d (d+t) (ℓ+1) (m+1) J (Nat.succ_le_succ hℓm))
    (actualPrincipalPartsTruncation_surjective d (d+t) (ℓ+1) (m+1) J (Nat.succ_le_succ hℓm))

end OriginalCentre

end
end Hironaka.HironakaActualCentrePrincipalPartsOrderSystem
