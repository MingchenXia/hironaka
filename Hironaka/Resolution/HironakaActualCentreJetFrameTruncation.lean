/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHSConstantCentreJetFrames
import Mathlib.Algebra.Module.Projective

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentreJetFrameTruncation
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaActualHSConstantCentreJetFrames HironakaRelativeNormalIdeal
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations
variable {n : ℕ}

/-- One genuine fixed complex-linear representative in the ENTIRE original germ ring, independent of all nearby points/families/pivots. -/
def actualScalarJetRepresentative (n q : ℕ) : scalarJetRange n q →ₗ[ℂ] HolGerm (ComplexModel n) :=
  Classical.choose ((scalarJet (n := n) q).rangeRestrict.exists_rightInverse_of_surjective
    (scalarJet (n := n) q).range_rangeRestrict)

/-- The actual original scalar jet of the chosen representative is literally its original image array. -/
theorem scalarJet_actualScalarJetRepresentative (n q : ℕ) (v : scalarJetRange n q) :
    scalarJet q (actualScalarJetRepresentative n q v)=(v : monomialIndex n q → ℂ) := by
  have h := LinearMap.congr_fun
    (Classical.choose_spec ((scalarJet (n := n) q).rangeRestrict.exists_rightInverse_of_surjective
      (scalarJet (n := n) q).range_rangeRestrict)) v
  exact congrArg Subtype.val h

/-- The true whole quotient coordinates of this fixed representative equal ANY original constant row-kernel vector. -/
theorem wholeCoordinates_fixed_representative (q : ℕ) {ι : Type*} [Fintype ι] (H : ι → ComplexModel n → ℂ)
    {k : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
    (p : ComplexModel n) (hdet : (pivotMatrix q H rows cols p).det ≠ 0)
    (hH : ∀ i,HolAt (H i) p) (v : fixedQuotientModel q rows) :
    wholeQuotientCoordinates q H rows cols p hdet hH
        (actualScalarJetRepresentative n q ⟨v,v.2.1⟩)=v := by
  apply Subtype.ext
  change pivotProjection q H rows cols p (scalarJet q (actualScalarJetRepresentative n q ⟨v,v.2.1⟩))=
    (v : monomialIndex n q → ℂ)
  rw [scalarJet_actualScalarJetRepresentative]
  exact pivotProjection_eq_self q H rows cols p v (LinearMap.mem_ker.mp v.2.2)

/-- The genuine whole-germ fixed representative followed by actual lower whole coordinates. -/
def actualJetFrameTruncation (q r : ℕ) {ι : Type*} [Fintype ι] (H : ι → ComplexModel n → ℂ)
    {k l : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
    (rows' : Fin l → monomialIndex n r) (p : ComplexModel n)
    (hdet : (pivotMatrix q H rows cols p).det ≠ 0) (hH : ∀ i,HolAt (H i) p) :
    fixedQuotientModel r rows' →ₗ[ℂ] fixedQuotientModel q rows :=
  (wholeQuotientCoordinates q H rows cols p hdet hH).comp
    ((actualScalarJetRepresentative n r).comp
      (Submodule.inclusion (show fixedQuotientModel r rows' ≤ scalarJetRange n r from inf_le_left)))

/-- The transition preserves EVERY true original numerator, through the ENTIRE upper/lower coordinate kernels. -/
theorem actualJetFrameTruncation_wholeCoordinates (q r : ℕ) (hqr : q ≤ r)
    {ι : Type*} [Fintype ι] (H : ι → ComplexModel n → ℂ)
    {k l : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
    (rows' : Fin l → monomialIndex n r) (cols' : Fin l → monomialIndex n r × ι)
    (p : ComplexModel n) (hdet : (pivotMatrix q H rows cols p).det ≠ 0)
    (hdet' : (pivotMatrix r H rows' cols' p).det ≠ 0) (hH : ∀ i,HolAt (H i) p)
    (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k)
    (hrank' : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap r H p))=l)
    (g : HolGerm (ComplexModel n)) :
    actualJetFrameTruncation q r H rows cols rows' p hdet hH
      (wholeQuotientCoordinates r H rows' cols' p hdet' hH g)=
        wholeQuotientCoordinates q H rows cols p hdet hH g := by
  let v := wholeQuotientCoordinates r H rows' cols' p hdet' hH g
  let f := actualScalarJetRepresentative n r ⟨v,v.2.1⟩
  have he : wholeQuotientCoordinates r H rows' cols' p hdet' hH f=
      wholeQuotientCoordinates r H rows' cols' p hdet' hH g :=
    wholeCoordinates_fixed_representative r H rows' cols' p hdet' hH v
  have hmem : f-g ∈ translatedIdeal H p hH ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ r := by
    have hz : wholeQuotientCoordinates r H rows' cols' p hdet' hH (f-g)=0 := by
      rw [map_sub,he,sub_self]
    have hh := LinearMap.mem_ker.mpr hz
    rw [ker_wholeQuotientCoordinates r H rows' cols' p hdet' hrank' hH] at hh
    exact hh
  have hi : translatedIdeal H p hH ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ r ≤
      translatedIdeal H p hH ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q :=
    sup_le_sup_left (Ideal.pow_le_pow_right hqr) _
  have hlo : f-g ∈ translatedIdeal H p hH ⊔
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := hi hmem
  have hz : wholeQuotientCoordinates q H rows cols p hdet hH (f-g)=0 := by
    apply LinearMap.mem_ker.mp
    rw [ker_wholeQuotientCoordinates q H rows cols p hdet hrank hH]
    exact hlo
  rw [map_sub,sub_eq_zero] at hz
  exact hz

/-- Genuine surjectivity is inherited from the entire lower quotient, not from selected column generators. -/
theorem actualJetFrameTruncation_surjective (q r : ℕ) (hqr : q ≤ r)
    {ι : Type*} [Fintype ι] (H : ι → ComplexModel n → ℂ)
    {k l : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
    (rows' : Fin l → monomialIndex n r) (cols' : Fin l → monomialIndex n r × ι)
    (p : ComplexModel n) (hdet : (pivotMatrix q H rows cols p).det ≠ 0)
    (hdet' : (pivotMatrix r H rows' cols' p).det ≠ 0) (hH : ∀ i,HolAt (H i) p)
    (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k)
    (hrank' : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap r H p))=l) :
    Function.Surjective (actualJetFrameTruncation q r H rows cols rows' p hdet hH) := by
  intro v
  obtain ⟨g,hg⟩ := wholeQuotientCoordinates_surjective q H rows cols p hdet hH v
  exact ⟨wholeQuotientCoordinates r H rows' cols' p hdet' hH g,
    (actualJetFrameTruncation_wholeCoordinates q r hqr H rows cols rows' cols' p hdet hdet' hH hrank hrank' g).trans hg⟩

private theorem cast_quotient_linearEquiv_mk {M V : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup V] [Module ℂ V]
    (L : M →ₗ[ℂ] V) (hs : Function.Surjective L) (J : Submodule ℂ M)
    (he : LinearMap.ker L=J) (g : M) :
    (cast (congrArg (fun S : Submodule ℂ M => (M ⧸ S) ≃ₗ[ℂ] V) he)
      (L.quotKerEquivOfSurjective hs)) (Submodule.Quotient.mk g)=L g := by
  subst J
  exact L.quotKerEquivOfSurjective_apply_mk hs g

private theorem wholeQuotientFrame_mk (q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel n → ℂ) {k : ℕ} (rows : Fin k → monomialIndex n q)
    (cols : Fin k → monomialIndex n q × ι) (p : ComplexModel n)
    (hdet : (pivotMatrix q H rows cols p).det ≠ 0)
    (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k)
    (hH : ∀ i,HolAt (H i) p) (g : HolGerm (ComplexModel n)) :
    wholeQuotientFrame q H rows cols p hdet hrank hH
      (Ideal.Quotient.mk (translatedIdeal H p hH ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) g)=
      wholeQuotientCoordinates q H rows cols p hdet hH g := by
  unfold wholeQuotientFrame
  exact cast_quotient_linearEquiv_mk _ _ _
    (ker_wholeQuotientCoordinates q H rows cols p hdet hrank hH) g


/-- The ENTIRE original quotient factor is surjective and equals the genuine fixed-representative frame transition. -/
theorem actualJetFrameTruncation_quotient_factor (q r : ℕ) (hqr : q ≤ r)
    {ι : Type*} [Fintype ι] (H : ι → ComplexModel n → ℂ)
    {k l : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
    (rows' : Fin l → monomialIndex n r) (cols' : Fin l → monomialIndex n r × ι)
    (p : ComplexModel n) (hdet : (pivotMatrix q H rows cols p).det ≠ 0)
    (hdet' : (pivotMatrix r H rows' cols' p).det ≠ 0) (hH : ∀ i,HolAt (H i) p)
    (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k)
    (hrank' : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap r H p))=l) :
    let hinc : translatedIdeal H p hH ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ r ≤
        translatedIdeal H p hH ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q :=
      sup_le_sup_left (Ideal.pow_le_pow_right hqr) _
    Function.Surjective (Ideal.Quotient.factorₐ ℂ hinc) ∧
      ∀ u,wholeQuotientFrame q H rows cols p hdet hrank hH (Ideal.Quotient.factorₐ ℂ hinc u)=
        actualJetFrameTruncation q r H rows cols rows' p hdet hH
          (wholeQuotientFrame r H rows' cols' p hdet' hrank' hH u) := by
  dsimp only
  have hinc : translatedIdeal H p hH ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ r ≤
      translatedIdeal H p hH ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q :=
    sup_le_sup_left (Ideal.pow_le_pow_right hqr) _
  refine ⟨Ideal.Quotient.factor_surjective hinc,?_⟩
  intro u
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective u
  change wholeQuotientFrame q H rows cols p hdet hrank hH
      (Ideal.Quotient.mk (translatedIdeal H p hH ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) g)=_
  rw [wholeQuotientFrame_mk,wholeQuotientFrame_mk]
  exact (actualJetFrameTruncation_wholeCoordinates q r hqr H rows cols rows' cols' p
    hdet hdet' hH hrank hrank' g).symm

/-- Literal transition entries are the true holomorphic original projection of a FIXED lower jet array. -/
theorem actualJetFrameTruncation_holomorphic_entries (q r : ℕ)
    {ι : Type*} [Fintype ι] (H : ι → ComplexModel n → ℂ)
    {k l : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
    (rows' : Fin l → monomialIndex n r) {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hH : ∀ i,DifferentiableOn ℂ (H i) U)
    (hdet : ∀ p ∈ U,(pivotMatrix q H rows cols p).det ≠ 0)
    (v : fixedQuotientModel r rows') (a : monomialIndex n q) :
    DifferentiableOn ℂ (fun p => pivotProjection q H rows cols p
      (scalarJet q (actualScalarJetRepresentative n r ⟨v,v.2.1⟩)) a) U ∧
      ∀ p (hp : p ∈ U) (hHp : ∀ i,HolAt (H i) p),
        (actualJetFrameTruncation q r H rows cols rows' p (hdet p hp) hHp v : monomialIndex n q → ℂ) a=
          pivotProjection q H rows cols p
            (scalarJet q (actualScalarJetRepresentative n r ⟨v,v.2.1⟩)) a := by
  exact ⟨pivotProjection_holomorphic_entries q H rows cols hU hH (Subset.refl U) hdet _ a,
    fun _ _ _ => rfl⟩

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY actual original HS-constant centre/coherence supplies ALL adjacent-order whole quotient truncations on true domains through0. -/
theorem exists_original_hs_constant_centre_adjacent_jet_truncations
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
      ∃ (U : Set (ComplexModel (d+t))), IsOpen U ∧ 0 ∈ U ∧ ∃ _hUT : U ⊆ Φ.target,
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        (∀ i,DifferentiableOn ℂ (H i) U) ∧
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
          ∀ ℓ : ℕ,∃ (k : ℕ) (rows : Fin k → monomialIndex (d+t) (ℓ+1))
            (cols : Fin k → monomialIndex (d+t) (ℓ+1) × Fin N)
            (l : ℕ) (rows' : Fin l → monomialIndex (d+t) (ℓ+2))
            (cols' : Fin l → monomialIndex (d+t) (ℓ+2) × Fin N),
            k=Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H 0)) ∧
            l=Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+2) H 0)) ∧
            ∃ D : Set (ComplexModel (d+t)),IsOpen D ∧ (0 : ComplexModel (d+t)) ∈ D ∧
            ∃ hDU : D ⊆ U,
              IsOpen ((tangentInclusion d t) ⁻¹' D) ∧ (0 : ComplexModel d) ∈ (tangentInclusion d t) ⁻¹' D ∧
            ∃ hdet : ∀ p ∈ D,(pivotMatrix (ℓ+1) H rows cols p).det ≠ 0,
            ∃ hdet' : ∀ p ∈ D,(pivotMatrix (ℓ+2) H rows' cols' p).det ≠ 0,
            ∃ hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
                Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=k,
            ∃ hrank' : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
                Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+2) H p))=l,
              (∀ (v : fixedQuotientModel (ℓ+2) rows') (a : monomialIndex (d+t) (ℓ+1)),
                DifferentiableOn ℂ (fun p => pivotProjection (ℓ+1) H rows cols p
                  (scalarJet (ℓ+1) (actualScalarJetRepresentative (d+t) (ℓ+2) ⟨v,v.2.1⟩)) a) D) ∧
              ∀ p (hp : p ∈ D) (hplane : p ∈ complexCoordinatePlane (d+t) d),
                Function.Surjective (actualJetFrameTruncation (ℓ+1) (ℓ+2) H rows cols rows' p
                  (hdet p hp) (hhol p (hDU hp))) ∧
                (∀ g,actualJetFrameTruncation (ℓ+1) (ℓ+2) H rows cols rows' p (hdet p hp) (hhol p (hDU hp))
                  (wholeQuotientCoordinates (ℓ+2) H rows' cols' p (hdet' p hp) (hhol p (hDU hp)) g)=
                    wholeQuotientCoordinates (ℓ+1) H rows cols p (hdet p hp) (hhol p (hDU hp)) g) ∧
                let hinc : translatedIdeal H p (hhol p (hDU hp)) ⊔
                    IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+2) ≤
                      translatedIdeal H p (hhol p (hDU hp)) ⊔
                        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+1) :=
                  sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ (ℓ+1))) _
                Function.Surjective (Ideal.Quotient.factorₐ ℂ hinc) ∧
                  ∀ u,wholeQuotientFrame (ℓ+1) H rows cols p (hdet p hp) (hrank p hp hplane) (hhol p (hDU hp))
                    (Ideal.Quotient.factorₐ ℂ hinc u)=
                      actualJetFrameTruncation (ℓ+1) (ℓ+2) H rows cols rows' p (hdet p hp) (hhol p (hDU hp))
                        (wholeQuotientFrame (ℓ+2) H rows' cols' p (hdet' p hp) (hrank' p hp hplane) (hhol p (hDU hp)) u) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hD,hR,hpiv⟩ :=
    exists_original_hs_constant_centre_origin_pivot_frames C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hD,hR,?_⟩
  intro ℓ
  obtain ⟨k,rows,cols,hk,D0,hD0,h0D0,hD0U,_hV0,_h0V0,hdet0,_hhol0,_hframes0⟩ := hpiv ℓ
  obtain ⟨l,rows',cols',hl,D1,hD1,h0D1,_hD1U,_hV1,_h0V1,hdet1,_hhol1,_hframes1⟩ := hpiv (ℓ+1)
  let D := D0 ∩ D1
  have hDo : IsOpen D := hD0.inter hD1
  have h0D : (0 : ComplexModel (d+t)) ∈ D := ⟨h0D0,h0D1⟩
  have hDU : D ⊆ U := fun _ hp => hD0U hp.1
  have hdet : ∀ p ∈ D,(pivotMatrix (ℓ+1) H rows cols p).det ≠ 0 := fun p hp => hdet0 p hp.1
  have hdet' : ∀ p ∈ D,(pivotMatrix (ℓ+2) H rows' cols' p).det ≠ 0 := fun p hp => hdet1 p hp.2
  have hrank : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=k :=
    fun p hp hplane => (hR p (hDU hp) hplane ℓ).trans hk.symm
  have hrank' : ∀ p ∈ D,p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+2) H p))=l :=
    fun p hp hplane => (hR p (hDU hp) hplane (ℓ+1)).trans hl.symm
  refine ⟨k,rows,cols,l,rows',cols',hk,hl,D,hDo,h0D,hDU,
    hDo.preimage (tangentInclusion d t).continuous,?_,hdet,hdet',hrank,hrank',?_,?_⟩
  · change tangentInclusion d t 0 ∈ D
    simpa only [map_zero] using h0D
  · intro v a
    exact (actualJetFrameTruncation_holomorphic_entries (ℓ+1) (ℓ+2) H rows cols rows' hDo
      (fun i => (hH i).mono hDU) hdet v a).1
  · intro p hp hplane
    exact ⟨actualJetFrameTruncation_surjective (ℓ+1) (ℓ+2) (Nat.le_succ (ℓ+1)) H rows cols rows' cols' p
        (hdet p hp) (hdet' p hp) (hhol p (hDU hp)) (hrank p hp hplane) (hrank' p hp hplane),
      actualJetFrameTruncation_wholeCoordinates (ℓ+1) (ℓ+2) (Nat.le_succ (ℓ+1)) H rows cols rows' cols' p
        (hdet p hp) (hdet' p hp) (hhol p (hDU hp)) (hrank p hp hplane) (hrank' p hp hplane),
      actualJetFrameTruncation_quotient_factor (ℓ+1) (ℓ+2) (Nat.le_succ (ℓ+1)) H rows cols rows' cols' p
        (hdet p hp) (hdet' p hp) (hhol p (hDU hp)) (hrank p hp hplane) (hrank' p hp hplane)⟩

end OriginalCentre
end
end Hironaka.HironakaActualCentreJetFrameTruncation
