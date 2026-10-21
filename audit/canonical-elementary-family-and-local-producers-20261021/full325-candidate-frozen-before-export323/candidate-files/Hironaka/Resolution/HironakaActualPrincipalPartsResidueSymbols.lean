/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualCentrePrincipalPartsOrderSystem
import Hironaka.Resolution.HironakaRelativeNormalFibreHilbertSamuel
import Mathlib.RingTheory.Flat.Equalizer
/-!
# Actual base-residue layers and symbols of joint principal parts

The numerator-preserving residue map on the entire original adic layer is an
isomorphism whenever the actual lower truncation is flat. Literal multiplication
by any normal-ideal member commutes with this map. The whole base-fibre action
is proved to factor through origin evaluation, rather than imposed as data.
Original coherent constant-Hilbert--Samuel centre geometry supplies bijectivity
of this same named map at every order for one unchanged actual joint ideal.

The fibre remains a quotient by the whole base maximal image in the joint germ
ring. Identification with the original unjoint zero-base germ ring and transport
through tangent cuts are separate assertions; general normal flatness remains open.
-/

set_option autoImplicit false
open Set Filter TensorProduct
open scoped Topology TensorProduct
namespace Hironaka.HironakaActualPrincipalPartsResidueSymbols
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalUniformTruncations HironakaRelativeNormalFibreHilbertSamuel
  HironakaRelativeNormalNearbyUniformRanks HironakaActualCentreJointJets
  HironakaActualCentrePrincipalParts HironakaActualCentrePrincipalPartsFree
  HironakaActualCentrePrincipalPartsOrderSystem
attribute [local instance] baseGermResidueAlgebra
section RelativeLayers
variable (d n : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) :=
  tangentAlgebra d n
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) :=
  IsScalarTower.of_algHom (tangentPullback d n)

/-- The actual whole residue-layer map, retaining every original numerator. -/
def originalResidueLayerMap (I : Ideal (HolGerm (ComplexModel (d+n)))) (q : ℕ) :
    (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalGradedPiece d n I q) →ₗ[ℂ]
      originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q := by
  let f := (originalNormalFibreTruncationAlgEquiv d n I (q+1)).toLinearMap.comp
    (AlgebraTensorModule.lTensor ℂ ℂ (originalNormalTruncationPieceInclusion d n I q))
  refine f.codRestrict ((originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q).restrictScalars ℂ) ?_
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w hz hw => simpa only [map_add] using
      ((originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q).restrictScalars ℂ).add_mem hz hw
  | tmul c v =>
    obtain ⟨g, hg, he⟩ := v.property
    have hv : v.val = Ideal.Quotient.mk (I ⊔ normalIdeal d n^(q+1)) g := he.symm
    change originalNormalFibreTruncationAlgEquiv d n I (q+1)
      (c ⊗ₜ[HolGerm (ComplexModel d)] v.val) ∈ _
    rw [hv, originalNormalFibreTruncationAlgEquiv_tmul_mk]
    exact ((originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q).restrictScalars ℂ).smul_mem c
      ⟨g, hg, rfl⟩

theorem originalResidueLayerMap_tmul_mk (I : Ideal (HolGerm (ComplexModel (d+n))))
    (q : ℕ) (c : ℂ) (g : HolGerm (ComplexModel (d+n))) (hg : g ∈ normalIdeal d n^q) :
    (originalResidueLayerMap d n I q
      (c ⊗ₜ[HolGerm (ComplexModel d)]
        ⟨Ideal.Quotient.mk (I ⊔ normalIdeal d n^(q+1)) g, ⟨g,hg,rfl⟩⟩)).val =
      c • Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^(q+1)) g := by
  change originalNormalFibreTruncationAlgEquiv d n I (q+1)
    (c ⊗ₜ[HolGerm (ComplexModel d)] Ideal.Quotient.mk (I ⊔ normalIdeal d n^(q+1)) g) = _
  exact originalNormalFibreTruncationAlgEquiv_tmul_mk d n I (q+1) c g

theorem originalResidueLayerMap_surjective (I : Ideal (HolGerm (ComplexModel (d+n)))) (q : ℕ) :
    Function.Surjective (originalResidueLayerMap d n I q) := by
  rintro ⟨v,hv⟩
  obtain ⟨g,hg,he⟩ := hv
  change g ∈ normalIdeal d n^q at hg
  refine ⟨(1 : ℂ) ⊗ₜ[HolGerm (ComplexModel d)]
    ⟨Ideal.Quotient.mk (I ⊔ normalIdeal d n^(q+1)) g, ⟨g,hg,rfl⟩⟩, ?_⟩
  apply Subtype.ext
  rw [originalResidueLayerMap_tmul_mk d n I q 1 g hg, one_smul]
  exact he

theorem originalResidueLayerMap_injective (I : Ideal (HolGerm (ComplexModel (d+n))))
    (q : ℕ) [Module.Flat (HolGerm (ComplexModel d)) (originalNormalTruncation d n I q)] :
    Function.Injective (originalResidueLayerMap d n I q) := by
  have hi := LinearMap.lTensor_injective_of_exact_of_flat
    (originalNormalTruncationMap d n I q).toLinearMap
    (originalNormalTruncationMap_surjective d n I q)
    (originalNormalTruncationPieceInclusion d n I q)
    (originalNormalTruncationPieceInclusion_injective d n I q)
    (originalNormalTruncation_exact d n I q) ℂ
  intro u v huv
  apply hi
  apply (originalNormalFibreTruncationAlgEquiv d n I (q+1)).injective
  exact congrArg Subtype.val huv

def originalResidueLayerEquiv (I : Ideal (HolGerm (ComplexModel (d+n))))
    (q : ℕ) [Module.Flat (HolGerm (ComplexModel d)) (originalNormalTruncation d n I q)] :
    (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalGradedPiece d n I q) ≃ₗ[ℂ]
      originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q :=
  LinearEquiv.ofBijective (originalResidueLayerMap d n I q)
    ⟨originalResidueLayerMap_injective d n I q, originalResidueLayerMap_surjective d n I q⟩


private theorem symbol_mul_denominator (I : Ideal (HolGerm (ComplexModel (d+n))))
    (v : HolGerm (ComplexModel (d+n))) (hv : v ∈ normalIdeal d n) (q : ℕ)
    (g : HolGerm (ComplexModel (d+n))) (hg : g ∈ I ⊔ normalIdeal d n^(q+1)) :
    v*g ∈ I ⊔ normalIdeal d n^(q+2) := by
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hg
  rw [mul_add]
  apply Ideal.add_mem
  · exact Ideal.mem_sup_left (I.mul_mem_left v ha)
  · apply Ideal.mem_sup_right
    rw [show q+2=(q+1)+1 from rfl,pow_succ']
    exact Ideal.mul_mem_mul hv hb

/-- Literal multiplication by an actual normal-ideal member on the whole original layers. -/
def originalLayerSymbolMul (I : Ideal (HolGerm (ComplexModel (d+n))))
    (v : HolGerm (ComplexModel (d+n))) (hv : v ∈ normalIdeal d n) (q : ℕ) :
    originalNormalGradedPiece d n I q →ₗ[HolGerm (ComplexModel d)]
      originalNormalGradedPiece d n I (q+1) := by
  let F := ((I ⊔ normalIdeal d n^(q+1)).restrictScalars (HolGerm (ComplexModel d))).liftQ
    ((Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (I ⊔ normalIdeal d n^(q+2))).toLinearMap.comp
      (LinearMap.mulLeft (HolGerm (ComplexModel d)) v))
    (by
      intro g hg
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact symbol_mul_denominator d n I v hv q g hg)
  refine (F.comp (originalNormalGradedPiece d n I q).subtype).codRestrict _ ?_
  rintro ⟨x,hx⟩
  obtain ⟨g,hg,rfl⟩ := hx
  refine ⟨v*g,?_,rfl⟩
  rw [pow_succ']
  exact Ideal.mul_mem_mul hv hg

@[simp] theorem originalLayerSymbolMul_mk (I : Ideal (HolGerm (ComplexModel (d+n))))
    (v : HolGerm (ComplexModel (d+n))) (hv : v ∈ normalIdeal d n) (q : ℕ)
    (g : HolGerm (ComplexModel (d+n))) (hg : g ∈ normalIdeal d n^q) :
    originalLayerSymbolMul d n I v hv q
      ⟨Ideal.Quotient.mk (I ⊔ normalIdeal d n^(q+1)) g,⟨g,hg,rfl⟩⟩ =
    ⟨Ideal.Quotient.mk (I ⊔ normalIdeal d n^(q+2)) (v*g),
      ⟨v*g,by rw [pow_succ']; exact Ideal.mul_mem_mul hv hg,rfl⟩⟩ := rfl

theorem originalResidueLayerMap_tmul (I : Ideal (HolGerm (ComplexModel (d+n))))
    (q : ℕ) (c : ℂ) (g : HolGerm (ComplexModel (d+n))) (hg : g ∈ normalIdeal d n^q) :
    originalResidueLayerMap d n I q
      (c ⊗ₜ[HolGerm (ComplexModel d)]
        ⟨Ideal.Quotient.mk (I ⊔ normalIdeal d n^(q+1)) g,⟨g,hg,rfl⟩⟩) =
    c • (⟨Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^(q+1)) g,
      ⟨g,hg,rfl⟩⟩ : originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q) := by
  apply Subtype.ext
  exact originalResidueLayerMap_tmul_mk d n I q c g hg

/-- The entire actual base maximal image makes the base action exactly its genuine residue evaluation. -/
theorem originalFibreLayer_base_smul (I : Ideal (HolGerm (ComplexModel (d+n))))
    (q : ℕ) (b : HolGerm (ComplexModel d))
    (z : originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q) :
    b • z = HolGerm.eval b • z := by
  apply Subtype.ext
  change Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^(q+1))
      (tangentPullback d n b) * z.val =
    Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^(q+1))
      (HolGerm.constHom (HolGerm.eval b)) * z.val
  congr 1
  apply Ideal.Quotient.eq.mpr
  have hb : b - algebraMap ℂ (HolGerm (ComplexModel d)) (HolGerm.eval b) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) := by
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    change HolGerm.eval (b - HolGerm.constHom (HolGerm.eval b)) = 0
    rw [map_sub, HolGerm.eval_constHom, sub_self]
  have hm := Ideal.mem_map_of_mem (tangentPullback d n).toRingHom hb
  change tangentPullback d n (b - algebraMap ℂ (HolGerm (ComplexModel d)) (HolGerm.eval b)) ∈
    originalBaseMaximalIdeal d n at hm
  rw [map_sub, (tangentPullback d n).commutes] at hm
  exact Ideal.mem_sup_left (Ideal.mem_sup_right hm)

/-- The actual whole base-fibre layer carries the proved residue-compatible scalar tower. -/
theorem originalFibreLayerScalarTower (I : Ideal (HolGerm (ComplexModel (d+n)))) (q : ℕ) :
    IsScalarTower (HolGerm (ComplexModel d)) ℂ
      (originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q) := by
  constructor
  intro b c z
  change (HolGerm.eval b * c) • z = b • (c • z)
  rw [originalFibreLayer_base_smul, mul_smul]

set_option maxHeartbeats 1000000 in
/-- The actual tensor symbol is the same whole multiplication on the genuine base fibre. -/
theorem originalResidueLayerMap_symbol (I : Ideal (HolGerm (ComplexModel (d+n))))
    (v : HolGerm (ComplexModel (d+n))) (hv : v ∈ normalIdeal d n) (q : ℕ)
    (z : ℂ ⊗[HolGerm (ComplexModel d)] originalNormalGradedPiece d n I q) :
    originalResidueLayerMap d n I (q+1)
      (AlgebraTensorModule.lTensor ℂ ℂ (originalLayerSymbolMul d n I v hv q) z) =
    originalLayerSymbolMul d n (I ⊔ originalBaseMaximalIdeal d n) v hv q
      (originalResidueLayerMap d n I q z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul c z =>
    rcases z with ⟨x,hx⟩
    obtain ⟨g,hg,rfl⟩ := hx
    change g ∈ normalIdeal d n^q at hg
    let a : originalNormalGradedPiece d n I q :=
      ⟨Ideal.Quotient.mk (I ⊔ normalIdeal d n^(q+1)) g,⟨g,hg,rfl⟩⟩
    let af : originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q :=
      ⟨Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^(q+1)) g,
        ⟨g,hg,rfl⟩⟩
    have hvg : v*g ∈ normalIdeal d n^(q+1) := by
      rw [pow_succ']; exact Ideal.mul_mem_mul hv hg
    let b : originalNormalGradedPiece d n I (q+1) :=
      ⟨Ideal.Quotient.mk (I ⊔ normalIdeal d n^(q+2)) (v*g),⟨v*g,hvg,rfl⟩⟩
    let bf : originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) (q+1) :=
      ⟨Ideal.Quotient.mk ((I ⊔ originalBaseMaximalIdeal d n) ⊔ normalIdeal d n^(q+2)) (v*g),
        ⟨v*g,hvg,rfl⟩⟩
    change originalResidueLayerMap d n I (q+1)
      (AlgebraTensorModule.lTensor ℂ ℂ (originalLayerSymbolMul d n I v hv q)
        (c ⊗ₜ[HolGerm (ComplexModel d)] a)) =
      originalLayerSymbolMul d n (I ⊔ originalBaseMaximalIdeal d n) v hv q
        (originalResidueLayerMap d n I q (c ⊗ₜ[HolGerm (ComplexModel d)] a))
    have hs : originalLayerSymbolMul d n I v hv q a = b :=
      originalLayerSymbolMul_mk d n I v hv q g hg
    have hsf : originalLayerSymbolMul d n (I ⊔ originalBaseMaximalIdeal d n) v hv q af = bf :=
      originalLayerSymbolMul_mk d n (I ⊔ originalBaseMaximalIdeal d n) v hv q g hg
    have hEf : originalResidueLayerMap d n I q (c ⊗ₜ[HolGerm (ComplexModel d)] a) = c • af :=
      originalResidueLayerMap_tmul d n I q c g hg
    have hEb : originalResidueLayerMap d n I (q+1) (c ⊗ₜ[HolGerm (ComplexModel d)] b) = c • bf :=
      originalResidueLayerMap_tmul d n I (q+1) c (v*g) hvg
    have hc : originalLayerSymbolMul d n (I ⊔ originalBaseMaximalIdeal d n) v hv q (c • af) = c • bf := by
      exact (((originalLayerSymbolMul d n (I ⊔ originalBaseMaximalIdeal d n) v hv q).restrictScalars ℂ).map_smul c af).trans
        (congrArg (fun z => c • z) hsf)
    calc
      _ = originalResidueLayerMap d n I (q+1)
          (c ⊗ₜ[HolGerm (ComplexModel d)] b) := by
        apply congrArg (originalResidueLayerMap d n I (q+1))
        exact (AlgebraTensorModule.lTensor_tmul (originalLayerSymbolMul d n I v hv q) c a).trans
          (congrArg (fun z => c ⊗ₜ[HolGerm (ComplexModel d)] z) hs)
      _ = c • bf := hEb
      _ = originalLayerSymbolMul d n (I ⊔ originalBaseMaximalIdeal d n) v hv q (c • af) := hc.symm
      _ = _ := congrArg (originalLayerSymbolMul d n (I ⊔ originalBaseMaximalIdeal d n) v hv q) hEf.symm


theorem allResidueLayers_of_projectiveTruncations
    (I : Ideal (HolGerm (ComplexModel (d+n))))
    (hproj : ∀ q : ℕ, Module.Projective (HolGerm (ComplexModel d))
      (originalNormalTruncation d n I (q+1))) :
    ∀ q : ℕ, Function.Bijective (originalResidueLayerMap d n I q) ∧
      Nonempty ((ℂ ⊗[HolGerm (ComplexModel d)] originalNormalGradedPiece d n I q) ≃ₗ[ℂ]
      originalNormalGradedPiece d n (I ⊔ originalBaseMaximalIdeal d n) q) := by
  intro q
  cases q with
  | zero =>
    let : Subsingleton (originalNormalTruncation d n I 0) :=
      originalNormalTruncation_zero_subsingleton d n I
    let : Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d n I 0) := inferInstance
    exact ⟨⟨originalResidueLayerMap_injective d n I 0, originalResidueLayerMap_surjective d n I 0⟩,
      ⟨originalResidueLayerEquiv d n I 0⟩⟩
  | succ q =>
    let := hproj q
    exact ⟨⟨originalResidueLayerMap_injective d n I (q+1), originalResidueLayerMap_surjective d n I (q+1)⟩,
      ⟨originalResidueLayerEquiv d n I (q+1)⟩⟩

end RelativeLayers
section OriginalCentre
open scoped Manifold ContDiff
open HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t)))) :=
  tangentAlgebra d (d+t)
local instance : IsScalarTower ℂ (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+(d+t)))) :=
  IsScalarTower.of_algHom (tangentPullback d (d+t))

set_option maxHeartbeats 1000000 in
/-- Only original constant-HS centre geometry supplies one unchanged joint family and every whole residue-layer equivalence. -/
theorem exists_original_hs_constant_centre_residue_layers
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ = hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ (O : Set M), IsOpen O ∧ x ∈ O ∧ ∃ (N : ℕ) (G : Fin N → M → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (G i) O) ∧
        (∀ y ∈ O, ∀ g, A.mem y g ↔ IsInSpanAt (n := d+t) (· ∈ Set.range G) y g) ∧
      ∃ (U : Set (ComplexModel (d+t))), IsOpen U ∧ 0 ∈ U ∧ ∃ _hUT : U ⊆ Φ.target,
        MapsTo (actualFlatteningInverseMap x Φ) U O ∧
        let H : Fin N → ComplexModel (d+t) → ℂ := fun i => G i ∘ actualFlatteningInverseMap x Φ
        (∀ i, DifferentiableOn ℂ (H i) U) ∧
        ∃ hhol : ∀ p ∈ U, ∀ i, HolAt (H i) p,
          (∀ p (hp : p ∈ U), originalCoherentOriginIdeal
            (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) p) =
              HironakaHolomorphicJetRankLoci.translatedIdeal H p (hhol p hp)) ∧
          ∃ hH0 : ∀ i, HolAt (H i) 0,
            let J := actualCentreJointIdeal d t H hH0
            ∀ q : ℕ, Function.Bijective (originalResidueLayerMap d (d+t) J q) ∧ Nonempty
              ((ℂ ⊗[HolGerm (ComplexModel d)] originalNormalGradedPiece d (d+t) J q) ≃ₗ[ℂ]
                originalNormalGradedPiece d (d+t) (J ⊔ originalBaseMaximalIdeal d (d+t)) q) := by
  obtain ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,
    _hHS,_hR,hH0,horders,_hpairs⟩ :=
    exists_original_hs_constant_centre_whole_split_order_system C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,O,hO,hxO,N,G,hG,hgen,U,hU,h0U,hUT,hMap,hH,hhol,hI,hH0,?_⟩
  apply allResidueLayers_of_projectiveTruncations
  intro q
  exact (horders q).2.1

end OriginalCentre
end
end Hironaka.HironakaActualPrincipalPartsResidueSymbols
