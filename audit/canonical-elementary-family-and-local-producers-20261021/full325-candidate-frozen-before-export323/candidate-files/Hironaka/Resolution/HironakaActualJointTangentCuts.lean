/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualJointBaseFibre
import Hironaka.Resolution.HironakaActualBaseResidueField
import Hironaka.Resolution.HironakaActualInitialCoordinateQuotient
import Hironaka.Resolution.HironakaActualCentreCoupledSymbols
/-!
# Actual finite free tangent cuts of the joint displacement filtration

The whole original ambient symbol dictionary and actual tensor square produce
complex-residue symbol injectivity. Actual short exact truncation sequences
retain freeness in both directions, and the canonical local residue criterion
then makes every whole layer finite free after each distinct coordinate cut.
Remaining initial-ideal derivative stability is proved after every actual cut.

The final original-only endpoint uses one coupled coherent constant-Hilbert--
Samuel family, with the actual origin ideal and actual joint extension. It
produces all-degree finite freeness after killing every tangent displacement.
No flatness, basis, initial-stability or symbol certificate is an input to this
geometric endpoint. Transport through the B-linear zero-displacement quotient
to the original centre-normal layers is a separate dictionary.
-/

set_option autoImplicit false
open Set Filter TensorProduct
open scoped Topology TensorProduct
namespace Hironaka.HironakaActualJointTangentCuts
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalUniformTruncations HironakaActualCentreJointJets
  HironakaActualPrincipalPartsResidueSymbols HironakaActualJointBaseFibre
  HironakaStrictFilteredGradedQuotient HironakaActualBaseResidueField
  HironakaActualHomogeneousInitialHS HironakaActualCoefficientPresentationCentrePower
  HironakaActualInitialSymbolRegularity HironakaActualInitialCoordinateQuotient
attribute [local instance] HironakaRelativeNormalNearbyUniformRanks.baseGermResidueAlgebra
private def wholeShortExactProductEquiv {B : Type*} [CommRing B]
    {L M N : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module B L] [Module B M] [Module B N] [Module.Projective B N]
    (g : L →ₗ[B] M) (h : M →ₗ[B] N) (hg : Function.Injective g)
    (hh : Function.Surjective h) (ex : Function.Exact g h) : M ≃ₗ[B] L × N := by
  let hex := Module.projective_lifting_property h (LinearMap.id : N →ₗ[B] N) hh
  let s := Classical.choose hex
  have hs := Classical.choose_spec hex
  have hsec : ∀ y, h (s y)=y := fun y => LinearMap.congr_fun hs y
  have hgzero : ∀ z, h (g z)=0 := fun z => (ex (g z)).mpr ⟨z,rfl⟩
  let gk : L →ₗ[B] LinearMap.ker h := g.codRestrict (LinearMap.ker h) hgzero
  have hgb : Function.Bijective gk := by
    constructor
    · intro x y hxy
      exact hg (congrArg Subtype.val hxy)
    · intro x
      obtain ⟨z,hz⟩ := (ex x.val).mp x.property
      exact ⟨z,Subtype.ext hz⟩
  let E := LinearEquiv.ofBijective gk hgb
  let k : M →ₗ[B] LinearMap.ker h :=
    (LinearMap.id-s.comp h).codRestrict (LinearMap.ker h) (fun x => by
      change h (x-s (h x))=0
      rw [map_sub,hsec,sub_self])
  let f : M →ₗ[B] L × N := (E.symm.toLinearMap.comp k).prod h
  let inv : L × N →ₗ[B] M := g.comp (LinearMap.fst B L N) + s.comp (LinearMap.snd B L N)
  have hfi : f.comp inv = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rcases x with ⟨z,y⟩
    change (E.symm (k (g z+s y)),h (g z+s y))=(z,y)
    apply Prod.ext
    · apply E.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      change (g z+s y)-s (h (g z+s y))=g z
      rw [map_add,hgzero,zero_add,hsec]
      abel
    · change h (g z+s y)=y
      rw [map_add,hgzero,hsec,zero_add]
  have hif : inv.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change g (E.symm (k x))+s (h x)=x
    have hk := congrArg Subtype.val (E.apply_symm_apply (k x))
    change g (E.symm (k x))=x-s (h x) at hk
    rw [hk]
    abel
  exact LinearEquiv.ofLinearMap f inv hfi hif


section Joint
set_option maxHeartbeats 1000000
variable (d n : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) := tangentAlgebra d n
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) :=
  IsScalarTower.of_algHom (tangentPullback d n)

theorem originalNormalGradedPiece_eq_adicLayer (K : Ideal (HolGerm (ComplexModel (d+n)))) (q : ℕ) :
    originalNormalGradedPiece d n K q =
      (adicLayer K (normalIdeal d n) q).restrictScalars (HolGerm (ComplexModel d)) := by
  ext x
  rfl

private theorem adicSymbolMul_injective_of_regular
    {R : Type*} [CommRing R] (I N : Ideal R) (v : R) (hv : v ∈ N) (q : ℕ)
    (hreg : ∀ b ∈ N^q, v*b ∈ I ⊔ N^(q+2) → b ∈ I ⊔ N^(q+1)) :
    Function.Injective (adicSymbolMul I N v hv q) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ hxy
  obtain ⟨g,hg,rfl⟩ := hx
  obtain ⟨h,hh,rfl⟩ := hy
  apply Subtype.ext
  apply Ideal.Quotient.eq.mpr
  apply hreg (g-h) ((N^q).sub_mem hg hh)
  have he : Ideal.Quotient.mk (I ⊔ N^(q+2)) (v*g)=
      Ideal.Quotient.mk (I ⊔ N^(q+2)) (v*h) := congrArg Subtype.val hxy
  simpa only [mul_sub] using Ideal.Quotient.eq.mp he

set_option maxHeartbeats 1000000 in
theorem complexTensorSymbol_injective_of_ambient_regular
    (K : Ideal (HolGerm (ComplexModel (d+n))))
    (v : HolGerm (ComplexModel (d+n))) (hv : v ∈ normalIdeal d n) (q : ℕ)
    [Module.Flat (HolGerm (ComplexModel d)) (originalNormalTruncation d n K q)]
    (hreg : ∀ b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q,
      jointBaseZeroTrace d n v*b ∈ Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(q+2) →
      b ∈ Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(q+1)) :
    Function.Injective (AlgebraTensorModule.lTensor ℂ ℂ (originalLayerSymbolMul d n K v hv q)) := by
  have ha := adicSymbolMul_injective_of_regular
    (Ideal.map (jointBaseZeroTrace d n).toRingHom K)
    (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)))
    (jointBaseZeroTrace d n v) (jointBaseZeroTrace_mem_maximalIdeal d n v hv) q hreg
  have hf : Function.Injective (originalLayerSymbolMul d n (K ⊔
      HironakaRelativeNormalFibreHilbertSamuel.originalBaseMaximalIdeal d n) v hv q) := by
    intro a b hab
    apply jointBaseFibreLayerMap_injective d n K q
    apply ha
    exact (jointBaseFibreLayerMap_symbol d n K v hv q a).symm.trans
      ((congrArg (jointBaseFibreLayerMap d n K (q+1)) hab).trans
        (jointBaseFibreLayerMap_symbol d n K v hv q b))
  intro a b hab
  apply originalResidueLayerMap_injective d n K q
  apply hf
  exact (originalResidueLayerMap_symbol d n K v hv q a).symm.trans
    ((congrArg (originalResidueLayerMap d n K (q+1)) hab).trans
      (originalResidueLayerMap_symbol d n K v hv q b))


theorem normalTruncations_free_of_layers (K : Ideal (HolGerm (ComplexModel (d+n))))
    (hfree : ∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d n) q)) :
    ∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d n K q) := by
  intro q
  induction q with
  | zero =>
    let : Subsingleton (originalNormalTruncation d n K 0) := originalNormalTruncation_zero_subsingleton d n K
    infer_instance
  | succ q ih =>
    let := ih
    let : Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d n K q) := by
      change Module.Free (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d n) q)
      exact hfree q
    let E := wholeShortExactProductEquiv (originalNormalTruncationPieceInclusion d n K q)
      (originalNormalTruncationMap d n K q).toLinearMap
      (originalNormalTruncationPieceInclusion_injective d n K q)
      (originalNormalTruncationMap_surjective d n K q) (originalNormalTruncation_exact d n K q)
    exact Module.Free.of_equiv E.symm

theorem normalLayers_finite_free_of_truncations (K : Ideal (HolGerm (ComplexModel (d+n))))
    (hQ : ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d n K q) ∧
      Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d n K q))
    (q : ℕ) :
    Module.Finite (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d n) q) ∧
      Module.Free (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d n) q) := by
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d n K q) := (hQ q).2
  let : Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d n K (q+1)) := (hQ (q+1)).1
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d n K (q+1)) := (hQ (q+1)).2
  let G := originalNormalGradedPiece d n K q
  let E := wholeShortExactProductEquiv (originalNormalTruncationPieceInclusion d n K q)
    (originalNormalTruncationMap d n K q).toLinearMap
    (originalNormalTruncationPieceInclusion_injective d n K q)
    (originalNormalTruncationMap_surjective d n K q) (originalNormalTruncation_exact d n K q)
  let r := (LinearMap.fst (HolGerm (ComplexModel d)) G (originalNormalTruncation d n K q)).comp E.toLinearMap
  let i := E.symm.toLinearMap.comp (LinearMap.inl (HolGerm (ComplexModel d)) G (originalNormalTruncation d n K q))
  have hri : r.comp i=LinearMap.id := by
    apply LinearMap.ext
    intro z
    change (E (E.symm (z,0))).1=z
    rw [E.apply_symm_apply]
  let : Module.Projective (HolGerm (ComplexModel d)) G := Module.Projective.of_split i r hri
  have hr : Function.Surjective r := by
    intro z
    refine ⟨i z,?_⟩
    exact LinearMap.congr_fun hri z
  let : Module.Finite (HolGerm (ComplexModel d)) G := Module.Finite.of_surjective r hr
  let : Module.Flat (HolGerm (ComplexModel d)) G := Module.Flat.of_projective
  let : Module.Free (HolGerm (ComplexModel d)) G := Module.free_of_flat_of_isLocalRing
  change Module.Finite (HolGerm (ComplexModel d)) G ∧ Module.Free (HolGerm (ComplexModel d)) G
  exact ⟨inferInstance,inferInstance⟩


theorem normalLayers_after_parameter_finite_free
    (K : Ideal (HolGerm (ComplexModel (d+n))))
    (v : HolGerm (ComplexModel (d+n))) (hv : v ∈ normalIdeal d n)
    (hfinite : ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d n) q))
    (hfree : ∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d n) q))
    (hreg : ∀ q : ℕ, ∀ b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q,
      jointBaseZeroTrace d n v*b ∈ Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(q+2) →
      b ∈ Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(q+1))
    (q : ℕ) :
    Module.Finite (HolGerm (ComplexModel d))
      (adicLayer (K ⊔ Ideal.span ({v} : Set (HolGerm (ComplexModel (d+n))))) (normalIdeal d n) q) ∧
    Module.Free (HolGerm (ComplexModel d))
      (adicLayer (K ⊔ Ideal.span ({v} : Set (HolGerm (ComplexModel (d+n))))) (normalIdeal d n) q) := by
  apply adicLayer_after_parameter_finite_free_of_complex d K (normalIdeal d n) v hv hfinite hfree
  intro r
  let : Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d n K r) :=
    normalTruncations_free_of_layers d n K hfree r
  change Function.Injective (AlgebraTensorModule.lTensor ℂ ℂ (originalLayerSymbolMul d n K v hv r))
  exact complexTensorSymbol_injective_of_ambient_regular d n K v hv r (hreg r)


/-- Ordered actual parameter-ideal cuts, retaining each entire ideal. -/
def parameterCuts {R : Type*} [CommRing R] {ι : Type*} (K : Ideal R) (v : ι → R) :
    List ι → Ideal R
  | [] => K
  | i :: L => parameterCuts (K ⊔ Ideal.span ({v i} : Set R)) v L


theorem initialideal_le_parameterCuts {R : Type*} [CommRing R] {ι : Type*}
    (K : Ideal R) (v : ι → R) (L : List ι) : K ≤ parameterCuts K v L := by
  induction L generalizing K with
  | nil => exact le_rfl
  | cons i L ih => exact le_sup_left.trans (ih (K ⊔ Ideal.span ({v i} : Set R)))

theorem parameter_mem_parameterCuts {R : Type*} [CommRing R] {ι : Type*}
    (K : Ideal R) (v : ι → R) (L : List ι) (j : ι) (hj : j ∈ L) :
    v j ∈ parameterCuts K v L := by
  induction L generalizing K with
  | nil => exact False.elim (List.not_mem_nil hj)
  | cons i L ih =>
    rcases List.mem_cons.mp hj with hji|hj
    · subst j
      apply initialideal_le_parameterCuts (K ⊔ Ideal.span ({v i} : Set R)) v L
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self (v i))
    · exact ih (K ⊔ Ideal.span ({v i} : Set R)) hj

theorem map_parameterCuts_zero {R S : Type*} [CommRing R] [CommRing S] {ι : Type*}
    (f : R →+* S) (K : Ideal R) (v : ι → R) (L : List ι)
    (hzero : ∀ i ∈ L, f (v i)=0) : Ideal.map f (parameterCuts K v L)=Ideal.map f K := by
  induction L generalizing K with
  | nil => rfl
  | cons i L ih =>
    change Ideal.map f (parameterCuts (K ⊔ Ideal.span ({v i} : Set R)) v L)=_
    rw [ih (K ⊔ Ideal.span ({v i} : Set R)) (fun j hj => hzero j (List.mem_cons_of_mem i hj))]
    rw [Ideal.map_sup,Ideal.map_span,Set.image_singleton,hzero i List.mem_cons_self,
      Ideal.span_singleton_zero,sup_bot_eq]

def jointCoordinateCuts (K : Ideal (HolGerm (ComplexModel (d+n)))) (L : List (Fin n)) :
    Ideal (HolGerm (ComplexModel (d+n))) := parameterCuts K (normalCoordinate d n) L

theorem map_jointCoordinateCuts (K : Ideal (HolGerm (ComplexModel (d+n)))) (L : List (Fin n)) :
    Ideal.map (jointBaseZeroTrace d n).toRingHom (jointCoordinateCuts d n K L)=
      parameterCuts (Ideal.map (jointBaseZeroTrace d n).toRingHom K) coordinateGerm L := by
  induction L generalizing K with
  | nil => rfl
  | cons i L ih =>
    change Ideal.map (jointBaseZeroTrace d n).toRingHom
      (jointCoordinateCuts d n (K ⊔ Ideal.span ({normalCoordinate d n i} : Set (HolGerm (ComplexModel (d+n))))) L)=_
    rw [ih,Ideal.map_sup,Ideal.map_span,Set.image_singleton]
    change parameterCuts (Ideal.map (jointBaseZeroTrace d n).toRingHom K ⊔
      Ideal.span ({jointBaseZeroTrace d n (normalCoordinate d n i)} : Set (HolGerm (ComplexModel n)))) coordinateGerm L=_
    rw [jointBaseZeroTrace_normalCoordinate]
    rfl

private theorem map_coordinate_cut_unshiftedTaylor (I : Ideal (HolGerm (ComplexModel n))) (i : Fin n) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (I ⊔ Ideal.span ({coordinateGerm i} : Set (HolGerm (ComplexModel n))))=
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I ⊔
      Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin n) ℂ)) := by
  rw [Ideal.map_sup,Ideal.map_span,Set.image_singleton]
  change Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I ⊔
    Ideal.span ({actualUnshiftedTaylorAlgHom n (coordinateGerm i)} : Set (MvPowerSeries (Fin n) ℂ))=_
  rw [actualUnshiftedTaylor_coordinate]

/-- Every distinct actual coordinate cut retains all whole displacement layers, using genuine original initial stability. -/
theorem normalLayers_after_coordinate_cuts_finite_free
    (K : Ideal (HolGerm (ComplexModel (d+n)))) (L : List (Fin n)) (hL : L.Nodup)
    (hfinite : ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d n) q))
    (hfree : ∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (adicLayer K (normalIdeal d n) q))
    (hD : ∀ i ∈ L, ∀ F ∈ actualHomogeneousInitialIdeal
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
        (Ideal.map (jointBaseZeroTrace d n).toRingHom K)),
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
          (Ideal.map (jointBaseZeroTrace d n).toRingHom K)))
    (q : ℕ) :
    Module.Finite (HolGerm (ComplexModel d)) (adicLayer (jointCoordinateCuts d n K L) (normalIdeal d n) q) ∧
      Module.Free (HolGerm (ComplexModel d)) (adicLayer (jointCoordinateCuts d n K L) (normalIdeal d n) q) := by
  induction L generalizing K with
  | nil => exact ⟨hfinite q,hfree q⟩
  | cons i L ih =>
    obtain ⟨hiL,hLn⟩ := List.nodup_cons.mp hL
    let I := Ideal.map (jointBaseZeroTrace d n).toRingHom K
    let F0 := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
    have hDi : ∀ P : MvPolynomial (Fin n) ℂ,
        (P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal F0 →
        (MvPolynomial.pderiv i P : MvPowerSeries (Fin n) ℂ) ∈ actualHomogeneousInitialIdeal F0 := by
      intro P hP
      rw [← MvPowerSeries.pderiv_coe]
      exact hD i List.mem_cons_self P hP
    let v := normalCoordinate d n i
    have hv : v ∈ normalIdeal d n := Ideal.subset_span ⟨i,rfl⟩
    have hreg (r : ℕ) (b : HolGerm (ComplexModel n))
        (hb : b ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^r)
        (hvb : jointBaseZeroTrace d n v*b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(r+2)) :
        b ∈ I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(r+1) := by
      dsimp only [v] at hvb
      rw [jointBaseZeroTrace_normalCoordinate] at hvb
      exact unshifted_original_regular_symbol_of_initial_pderiv n I i hDi r b hb hvb
    have hnew := normalLayers_after_parameter_finite_free d n K v hv hfinite hfree hreg
    have himage : Ideal.map (jointBaseZeroTrace d n).toRingHom
        (K ⊔ Ideal.span ({v} : Set (HolGerm (ComplexModel (d+n)))))=
      I ⊔ Ideal.span ({coordinateGerm i} : Set (HolGerm (ComplexModel n))) := by
      rw [Ideal.map_sup,Ideal.map_span,Set.image_singleton]
      change I ⊔ Ideal.span ({jointBaseZeroTrace d n (normalCoordinate d n i)} : Set (HolGerm (ComplexModel n)))=_
      rw [jointBaseZeroTrace_normalCoordinate]
    have hDtail : ∀ j ∈ L, ∀ F ∈ actualHomogeneousInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
          (Ideal.map (jointBaseZeroTrace d n).toRingHom
            (K ⊔ Ideal.span ({v} : Set (HolGerm (ComplexModel (d+n))))))),
        MvPowerSeries.pderiv ℂ j F ∈ actualHomogeneousInitialIdeal
          (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
            (Ideal.map (jointBaseZeroTrace d n).toRingHom
              (K ⊔ Ideal.span ({v} : Set (HolGerm (ComplexModel (d+n))))))) := by
      intro j hj F hF
      rw [himage,map_coordinate_cut_unshiftedTaylor] at hF ⊢
      have hij : i ≠ j := by intro he; subst j; exact hiL hj
      exact actualInitialIdeal_add_coordinate_pderiv F0 i j hij hDi
        (hD j (List.mem_cons_of_mem i hj)) F hF
    exact ih (K ⊔ Ideal.span ({v} : Set (HolGerm (ComplexModel (d+n))))) hLn
      (fun r => (hnew r).1) (fun r => (hnew r).2) hDtail

end Joint

section OriginalCentre
open scoped Manifold ContDiff
open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaActualCentrePrincipalParts HironakaActualCentreCoupledSymbols
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t)))) := tangentAlgebra d (d+t)
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t)))) :=
  IsScalarTower.of_algHom (tangentPullback d (d+t))
set_option maxHeartbeats 1000000

theorem exists_original_hs_constant_centre_all_tangent_cut_layers_free
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      let J := Ideal.map (actualCentreJointPullback d t).toRingHom I0
      let L := List.ofFn (fun i : Fin d => i.castAdd t)
      ∀ q : ℕ,
        Module.Finite (HolGerm (ComplexModel d))
          (adicLayer (jointCoordinateCuts d (d+t) J L) (normalIdeal d (d+t)) q) ∧
        Module.Free (HolGerm (ComplexModel d))
          (adicLayer (jointCoordinateCuts d (d+t) J L) (normalIdeal d (d+t)) q) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,_hO,_hxO,N,G,_hG,_hgen,U,_hU,_h0U,_hUT,
    _hMap,_hH,_hhol,_hI,hH0,hspan,horders,hD,_hDP⟩ :=
    exists_original_hs_constant_centre_coupled_symbols C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,?_⟩
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
  let J := Ideal.map (actualCentreJointPullback d t).toRingHom I0
  have hJ : J=actualCentreJointIdeal d t H hH0 := by
    dsimp only [J,I0]
    rw [hspan,Ideal.map_span,← Set.range_comp]
    rfl
  have hQ : ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d (d+t) J q) ∧
      Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d (d+t) J q) := by
    intro q
    cases q with
    | zero =>
      let : Subsingleton (originalNormalTruncation d (d+t) J 0) := originalNormalTruncation_zero_subsingleton d (d+t) J
      exact ⟨inferInstance,inferInstance⟩
    | succ q =>
      change Module.Finite (HolGerm (ComplexModel d))
          (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t)^(q+1))) ∧
        Module.Free (HolGerm (ComplexModel d))
          (HolGerm (ComplexModel (d+(d+t))) ⧸ (J ⊔ normalIdeal d (d+t)^(q+1)))
      rw [hJ]
      exact ⟨(horders q).1,(horders q).2.2⟩
  have hG := normalLayers_finite_free_of_truncations d (d+t) J hQ
  have hL : (List.ofFn (fun i : Fin d => i.castAdd t)).Nodup :=
    List.nodup_ofFn.mpr (Fin.castAdd_injective d t)
  intro q
  apply normalLayers_after_coordinate_cuts_finite_free d (d+t) J _ hL
    (fun q => (hG q).1) (fun q => (hG q).2)
  intro i hi F hF
  have hi' : ∃ j : Fin d, j.castAdd t=i := List.mem_ofFn.mp hi
  obtain ⟨j,rfl⟩ := hi'
  have hmap : Ideal.map (jointBaseZeroTrace d (d+t)).toRingHom J=I0 := map_jointIdeal_eq_original d t I0
  rw [hmap] at hF ⊢
  exact hD j F hF

end OriginalCentre
end
end Hironaka.HironakaActualJointTangentCuts
