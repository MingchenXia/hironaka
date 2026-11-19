/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentrePrincipalPartsOrderSystem
import Hironaka.Resolution.HironakaRelativeNormalAssociatedGraded

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentrePrincipalPartsGraded
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaActualCentreJointJets HironakaActualCentrePrincipalParts
  HironakaActualCentrePrincipalPartsFree HironakaActualCentrePrincipalPartsOrderSystem
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetQuotientFrames HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- BOTH whole submodules coincide: actual adjacent truncation kernel and EXISTING literal original displacement-graded power image. -/
theorem ker_actualPrincipalPartsTruncation_eq_originalGradedPiece (d n q : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) :
    let := tangentAlgebra d n
    LinearMap.ker (actualPrincipalPartsTruncation d n q (q+1) J (Nat.le_succ q))=
      originalNormalGradedPiece d n J q := by
  let := tangentAlgebra d n
  dsimp only
  ext v
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective v
  constructor
  · intro hg
    have hm : g ∈ J ⊔ normalIdeal d n ^ q :=
      Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hg)
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hm
    refine ⟨b,hb,?_⟩
    change Ideal.Quotient.mk (J ⊔ normalIdeal d n ^ (q+1)) b=
      Ideal.Quotient.mk (J ⊔ normalIdeal d n ^ (q+1)) g
    apply Ideal.Quotient.eq.mpr
    have he : b-g = -a := by rw [← hab]; abel
    rw [he]
    exact Ideal.mem_sup_left (J.neg_mem ha)
  · intro hg
    obtain ⟨b,hb,hbg⟩ := hg
    change Ideal.Quotient.mk (J ⊔ normalIdeal d n ^ (q+1)) b=
      Ideal.Quotient.mk (J ⊔ normalIdeal d n ^ (q+1)) g at hbg
    have hm : g-b ∈ J ⊔ normalIdeal d n ^ (q+1) := by
      have hz := (J ⊔ normalIdeal d n ^ (q+1)).neg_mem (Ideal.Quotient.eq.mp hbg)
      simpa only [neg_sub] using hz
    have hl : g-b ∈ J ⊔ normalIdeal d n ^ q :=
      (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ q)) J) hm
    have hg' : g ∈ J ⊔ normalIdeal d n ^ q := by
      have hh := (J ⊔ normalIdeal d n ^ q).add_mem hl (Ideal.mem_sup_right hb)
      simpa only [sub_add_cancel] using hh
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (J ⊔ normalIdeal d n ^ q) g=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hg'

/-- Canonical genuine original B-linear graded identification; no independent graded model is introduced. -/
def actualPrincipalPartsKernelGradedEquiv (d n q : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) :
    letI := tangentAlgebra d n
    LinearMap.ker (actualPrincipalPartsTruncation d n q (q+1) J (Nat.le_succ q)) ≃ₗ[HolGerm (ComplexModel d)]
      originalNormalGradedPiece d n J q :=
  letI := tangentAlgebra d n
  LinearEquiv.ofEq _ _ (ker_actualPrincipalPartsTruncation_eq_originalGradedPiece d n q J)

/-- EVERY whole original numerator class is unchanged by the canonical graded equivalence. -/
theorem actualPrincipalPartsKernelGradedEquiv_apply (d n q : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) :
    let := tangentAlgebra d n
    ∀ v : LinearMap.ker (actualPrincipalPartsTruncation d n q (q+1) J (Nat.le_succ q)),
      (actualPrincipalPartsKernelGradedEquiv d n q J v).val=v.val := by
  let := tangentAlgebra d n
  dsimp only
  intro v
  rfl

/-- Degree0 is the ENTIRE original first principal-parts quotient, not an omitted boundary case. -/
theorem originalNormalGradedPiece_zero_eq_top (d n : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) :
    let := tangentAlgebra d n
    originalNormalGradedPiece d n J 0=⊤ := by
  let := tangentAlgebra d n
  dsimp only
  change ((normalIdeal d n ^ 0).restrictScalars (HolGerm (ComplexModel d))).map
    (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (J ⊔ normalIdeal d n ^ (0+1))).toLinearMap=⊤
  rw [pow_zero,Ideal.one_eq_top,Submodule.restrictScalars_top,Submodule.map_top]
  exact LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective

/-- The literal cutoff0 principal-parts quotient is zero; this boundary is not inferred from positive-cutoff data. -/
theorem actualPrincipalPartsZero_subsingleton (d n : ℕ)
    (J : Ideal (HolGerm (ComplexModel (d+n)))) :
    Subsingleton (HolGerm (ComplexModel (d+n)) ⧸ (J ⊔ normalIdeal d n ^ 0)) := by
  rw [pow_zero,Ideal.one_eq_top,sup_top_eq]
  infer_instance

section OriginalCentre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ONLY original coherent HSconstant geometry gives SAME joint J and EVERY EXISTING literal displacement-graded layer finite projective/free, including degree0. -/
theorem exists_original_hs_constant_centre_displacement_graded_free
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
          ∀ q : ℕ,Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) J q) ∧
            Module.Projective (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) J q) ∧
            Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d (d+t) J q) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hHS,hR,hH0,horders,hpairs⟩ :=
    exists_original_hs_constant_centre_whole_split_order_system C x hreg A hA hhs
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  refine ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hHS,hR,hH0,?_⟩
  let := tangentAlgebra d (d+t)
  let J := actualCentreJointIdeal d t H hH0
  dsimp only
  intro q
  cases q with
  | zero =>
    have hf := horders 0
    let Q := HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t) ^ (0+1))
    let : Module.Finite (HolGerm (ComplexModel d)) Q := hf.1
    let : Module.Projective (HolGerm (ComplexModel d)) Q := hf.2.1
    let : Module.Free (HolGerm (ComplexModel d)) Q := hf.2.2
    let E := LinearEquiv.ofTop (originalNormalGradedPiece d (d+t) J 0)
      (originalNormalGradedPiece_zero_eq_top d (d+t) J)
    exact ⟨Module.Finite.equiv E.symm,Module.Projective.of_equiv E.symm,Module.Free.of_equiv E.symm⟩
  | succ a =>
    obtain ⟨s,_hs,hf,hp,he⟩ := hpairs a (a+1) (Nat.le_succ a)
    let K := LinearMap.ker (actualPrincipalPartsTruncation d (d+t) (a+1) ((a+1)+1) J (Nat.le_succ (a+1)))
    let : Module.Finite (HolGerm (ComplexModel d)) K := hf
    let : Module.Projective (HolGerm (ComplexModel d)) K := hp
    let : Module.Free (HolGerm (ComplexModel d)) K := he
    let E := actualPrincipalPartsKernelGradedEquiv d (d+t) (a+1) J
    exact ⟨Module.Finite.equiv E,Module.Projective.of_equiv E,Module.Free.of_equiv E⟩

end OriginalCentre

end
end Hironaka.HironakaActualCentrePrincipalPartsGraded
