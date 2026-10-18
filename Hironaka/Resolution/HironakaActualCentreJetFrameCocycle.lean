/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentreJetFrameTruncation

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentreJetFrameCocycle
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaActualHSConstantCentreJetFrames HironakaActualCentreJetFrameTruncation
  HironakaRelativeNormalIdeal HironakaSmoothCentreCoherentDomain
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
variable {n : ℕ}

/-- At equal orders, the literal original whole-representative transition is the identity. -/
theorem actualJetFrameTruncation_refl (q : ℕ) {ι : Type*} [Fintype ι]
    (H : ι → ComplexModel n → ℂ) {k : ℕ} (rows : Fin k → monomialIndex n q)
    (cols : Fin k → monomialIndex n q × ι) (p : ComplexModel n)
    (hdet : (pivotMatrix q H rows cols p).det ≠ 0) (hH : ∀ i,HolAt (H i) p) :
    actualJetFrameTruncation q q H rows cols rows p hdet hH=LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact wholeCoordinates_fixed_representative q H rows cols p hdet hH v

/-- The three-order cocycle holds on the ENTIRE original upper model, using one SAME numerator. -/
theorem actualJetFrameTruncation_comp (q r s : ℕ) (hqr : q ≤ r) (hrs : r ≤ s)
    {ι : Type*} [Fintype ι] (H : ι → ComplexModel n → ℂ)
    {k l m : ℕ} (rows : Fin k → monomialIndex n q) (cols : Fin k → monomialIndex n q × ι)
    (rows' : Fin l → monomialIndex n r) (cols' : Fin l → monomialIndex n r × ι)
    (rows'' : Fin m → monomialIndex n s) (cols'' : Fin m → monomialIndex n s × ι)
    (p : ComplexModel n) (hdet : (pivotMatrix q H rows cols p).det ≠ 0)
    (hdet' : (pivotMatrix r H rows' cols' p).det ≠ 0)
    (hdet'' : (pivotMatrix s H rows'' cols'' p).det ≠ 0) (hH : ∀ i,HolAt (H i) p)
    (hrank : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap q H p))=k)
    (hrank' : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap r H p))=l)
    (hrank'' : Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap s H p))=m) :
    (actualJetFrameTruncation q r H rows cols rows' p hdet hH).comp
      (actualJetFrameTruncation r s H rows' cols' rows'' p hdet' hH)=
        actualJetFrameTruncation q s H rows cols rows'' p hdet hH := by
  apply LinearMap.ext
  intro v
  obtain ⟨g,rfl⟩ := wholeQuotientCoordinates_surjective s H rows'' cols'' p hdet'' hH v
  change actualJetFrameTruncation q r H rows cols rows' p hdet hH
      (actualJetFrameTruncation r s H rows' cols' rows'' p hdet' hH
        (wholeQuotientCoordinates s H rows'' cols'' p hdet'' hH g))=_
  rw [actualJetFrameTruncation_wholeCoordinates r s hrs H rows' cols' rows'' cols'' p hdet' hdet'' hH hrank' hrank'',
    actualJetFrameTruncation_wholeCoordinates q r hqr H rows cols rows' cols' p hdet hdet' hH hrank hrank',
    actualJetFrameTruncation_wholeCoordinates q s (hqr.trans hrs) H rows cols rows'' cols'' p hdet hdet'' hH hrank hrank'']


section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original HS-constant geometry supplies one SAME orderwise choice before every whole quotient pair/triple. -/
theorem exists_original_hs_constant_centre_orderwise_jet_system
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
          ∃ (k : ℕ → ℕ) (rows : ∀ ℓ,Fin (k ℓ) → monomialIndex (d+t) (ℓ+1))
            (cols : ∀ ℓ,Fin (k ℓ) → monomialIndex (d+t) (ℓ+1) × Fin N)
            (D : ℕ → Set (ComplexModel (d+t))),
            (∀ ℓ,k ℓ=Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H 0))) ∧
            (∀ ℓ,IsOpen (D ℓ)) ∧ (∀ ℓ,(0 : ComplexModel (d+t)) ∈ D ℓ) ∧
            ∃ hDU : ∀ ℓ,D ℓ ⊆ U,
            ∃ hdet : ∀ ℓ p,p ∈ D ℓ → (pivotMatrix (ℓ+1) H (rows ℓ) (cols ℓ) p).det ≠ 0,
            ∃ hrank : ∀ ℓ p,p ∈ D ℓ → p ∈ complexCoordinatePlane (d+t) d →
                Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=k ℓ,
              (∀ ℓ p (hp : p ∈ D ℓ),
                actualJetFrameTruncation (ℓ+1) (ℓ+1) H (rows ℓ) (cols ℓ) (rows ℓ) p
                  (hdet ℓ p hp) (hhol p (hDU ℓ hp))=LinearMap.id) ∧
              (∀ i j (hij : i ≤ j),
                IsOpen (D i ∩ D j) ∧ (0 : ComplexModel (d+t)) ∈ D i ∩ D j ∧
                IsOpen ((tangentInclusion d t) ⁻¹' (D i ∩ D j)) ∧
                  (0 : ComplexModel d) ∈ (tangentInclusion d t) ⁻¹' (D i ∩ D j) ∧
                (∀ (v : fixedQuotientModel (j+1) (rows j)) (a : monomialIndex (d+t) (i+1)),
                  DifferentiableOn ℂ (fun p => pivotProjection (i+1) H (rows i) (cols i) p
                    (scalarJet (i+1) (actualScalarJetRepresentative (d+t) (j+1) ⟨v,v.2.1⟩)) a) (D i ∩ D j)) ∧
                ∀ p (hp : p ∈ D i ∩ D j) (hplane : p ∈ complexCoordinatePlane (d+t) d),
                  Function.Surjective (actualJetFrameTruncation (i+1) (j+1) H (rows i) (cols i) (rows j) p
                    (hdet i p hp.1) (hhol p (hDU i hp.1))) ∧
                  (∀ g,actualJetFrameTruncation (i+1) (j+1) H (rows i) (cols i) (rows j) p
                      (hdet i p hp.1) (hhol p (hDU i hp.1))
                      (wholeQuotientCoordinates (j+1) H (rows j) (cols j) p
                        (hdet j p hp.2) (hhol p (hDU i hp.1)) g)=
                    wholeQuotientCoordinates (i+1) H (rows i) (cols i) p
                      (hdet i p hp.1) (hhol p (hDU i hp.1)) g) ∧
                  let hinc : translatedIdeal H p (hhol p (hDU i hp.1)) ⊔
                      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (j+1) ≤
                        translatedIdeal H p (hhol p (hDU i hp.1)) ⊔
                          IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (i+1) :=
                    sup_le_sup_left (Ideal.pow_le_pow_right (Nat.add_le_add_right hij 1)) _
                  Function.Surjective (Ideal.Quotient.factorₐ ℂ hinc) ∧
                    ∀ u,wholeQuotientFrame (i+1) H (rows i) (cols i) p
                        (hdet i p hp.1) (hrank i p hp.1 hplane) (hhol p (hDU i hp.1))
                        (Ideal.Quotient.factorₐ ℂ hinc u)=
                      actualJetFrameTruncation (i+1) (j+1) H (rows i) (cols i) (rows j) p
                        (hdet i p hp.1) (hhol p (hDU i hp.1))
                        (wholeQuotientFrame (j+1) H (rows j) (cols j) p
                          (hdet j p hp.2) (hrank j p hp.2 hplane) (hhol p (hDU i hp.1)) u)) ∧
              ∀ i j l (_hij : i ≤ j) (_hjl : j ≤ l),
                IsOpen (D i ∩ D j ∩ D l) ∧ (0 : ComplexModel (d+t)) ∈ D i ∩ D j ∩ D l ∧
                IsOpen ((tangentInclusion d t) ⁻¹' (D i ∩ D j ∩ D l)) ∧
                  (0 : ComplexModel d) ∈ (tangentInclusion d t) ⁻¹' (D i ∩ D j ∩ D l) ∧
                ∀ p (hp : p ∈ D i ∩ D j ∩ D l) (_hplane : p ∈ complexCoordinatePlane (d+t) d),
                  (actualJetFrameTruncation (i+1) (j+1) H (rows i) (cols i) (rows j) p
                    (hdet i p hp.1.1) (hhol p (hDU i hp.1.1))).comp
                    (actualJetFrameTruncation (j+1) (l+1) H (rows j) (cols j) (rows l) p
                      (hdet j p hp.1.2) (hhol p (hDU i hp.1.1)))=
                    actualJetFrameTruncation (i+1) (l+1) H (rows i) (cols i) (rows l) p
                      (hdet i p hp.1.1) (hhol p (hDU i hp.1.1)) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hD,hR,hpiv⟩ :=
    exists_original_hs_constant_centre_origin_pivot_frames C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  choose k rows cols hk D hDo h0D hDU _hVo _h0V hdet _hproj _hframes using hpiv
  have hrank : ∀ ℓ p,p ∈ D ℓ → p ∈ complexCoordinatePlane (d+t) d →
      Module.finrank ℂ (LinearMap.range (originalMacaulayLinearMap (ℓ+1) H p))=k ℓ :=
    fun ℓ p hp hplane => (hR p (hDU ℓ hp) hplane ℓ).trans (hk ℓ).symm
  refine ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hD,hR,
    k,rows,cols,D,hk,hDo,h0D,hDU,hdet,hrank,?_,?_,?_⟩
  · intro ℓ p hp
    exact actualJetFrameTruncation_refl (ℓ+1) H (rows ℓ) (cols ℓ) p (hdet ℓ p hp) (hhol p (hDU ℓ hp))
  · intro i j hij
    have hE : IsOpen (D i ∩ D j) := (hDo i).inter (hDo j)
    have hEU : D i ∩ D j ⊆ U := fun _ hp => hDU i hp.1
    have hde : ∀ p ∈ D i ∩ D j,(pivotMatrix (i+1) H (rows i) (cols i) p).det ≠ 0 :=
      fun p hp => hdet i p hp.1
    refine ⟨hE,⟨h0D i,h0D j⟩,hE.preimage (tangentInclusion d t).continuous,?_,?_,?_⟩
    · change tangentInclusion d t 0 ∈ D i ∩ D j
      simpa only [map_zero] using (show (0 : ComplexModel (d+t)) ∈ D i ∩ D j from ⟨h0D i,h0D j⟩)
    · intro v a
      exact (actualJetFrameTruncation_holomorphic_entries (i+1) (j+1) H (rows i) (cols i) (rows j) hE
        (fun a => (hH a).mono hEU) hde v a).1
    · intro p hp hplane
      exact ⟨actualJetFrameTruncation_surjective (i+1) (j+1) (Nat.add_le_add_right hij 1) H
          (rows i) (cols i) (rows j) (cols j) p (hdet i p hp.1) (hdet j p hp.2)
          (hhol p (hDU i hp.1)) (hrank i p hp.1 hplane) (hrank j p hp.2 hplane),
        actualJetFrameTruncation_wholeCoordinates (i+1) (j+1) (Nat.add_le_add_right hij 1) H
          (rows i) (cols i) (rows j) (cols j) p (hdet i p hp.1) (hdet j p hp.2)
          (hhol p (hDU i hp.1)) (hrank i p hp.1 hplane) (hrank j p hp.2 hplane),
        actualJetFrameTruncation_quotient_factor (i+1) (j+1) (Nat.add_le_add_right hij 1) H
          (rows i) (cols i) (rows j) (cols j) p (hdet i p hp.1) (hdet j p hp.2)
          (hhol p (hDU i hp.1)) (hrank i p hp.1 hplane) (hrank j p hp.2 hplane)⟩
  · intro i j l hij hjl
    have hE : IsOpen (D i ∩ D j ∩ D l) := ((hDo i).inter (hDo j)).inter (hDo l)
    refine ⟨hE,⟨⟨h0D i,h0D j⟩,h0D l⟩,hE.preimage (tangentInclusion d t).continuous,?_,?_⟩
    · change tangentInclusion d t 0 ∈ D i ∩ D j ∩ D l
      simpa only [map_zero] using
        (show (0 : ComplexModel (d+t)) ∈ D i ∩ D j ∩ D l from ⟨⟨h0D i,h0D j⟩,h0D l⟩)
    · intro p hp hplane
      exact actualJetFrameTruncation_comp (i+1) (j+1) (l+1) (Nat.add_le_add_right hij 1)
        (Nat.add_le_add_right hjl 1) H (rows i) (cols i) (rows j) (cols j) (rows l) (cols l) p
        (hdet i p hp.1.1) (hdet j p hp.1.2) (hdet l p hp.2) (hhol p (hDU i hp.1.1))
        (hrank i p hp.1.1 hplane) (hrank j p hp.1.2 hplane) (hrank l p hp.2 hplane)

end OriginalCentre
end
end Hironaka.HironakaActualCentreJetFrameCocycle
