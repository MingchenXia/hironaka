/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalActualWeightedTruncations
import Hironaka.Resolution.HironakaRelativeNormalMonomialBasis
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset

/-! Genuine distinct-monomial dimensions of the ACTUAL original complex base jets. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalActualBaseJetDimension
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalFibreHilbertSamuel
  HironakaRelativeNormalMonomialBasis

/-- The unique actual zero-dimensional model point forces genuine evaluation injectivity. -/
theorem zeroBaseEval_injective :
    Function.Injective (HolGerm.eval : HolGerm (ComplexModel 0) →+* ℂ) := by
  intro g h he
  induction g using HolGerm.induction_on with
  | h f hf =>
    induction h using HolGerm.induction_on with
    | h g hg =>
      apply HolGerm.mk_eq_mk_iff.mpr
      apply Eventually.of_forall
      intro z
      have hz : z = (0 : ComplexModel 0) := Subsingleton.elim _ _
      rw [hz]
      exact he

/-- The evaluation algebra hom uses the SAME original constant-germ complex action. -/
def zeroBaseComplexEval : HolGerm (ComplexModel 0) →ₐ[ℂ] ℂ := by
  refine { (HolGerm.eval : HolGerm (ComplexModel 0) →+* ℂ) with commutes' := ?_ }
  intro c
  rfl

/-- The genuine zero-dimensional germ algebra is the ORIGINAL complex field. -/
def zeroBaseComplexAlgEquiv : HolGerm (ComplexModel 0) ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofBijective zeroBaseComplexEval
    ⟨zeroBaseEval_injective,fun c => ⟨HolGerm.constHom c,rfl⟩⟩

/-- The genuine original maximal ideal in dimension zero has no nonzero germ. -/
theorem zeroBaseMaximalIdeal_eq_bot :
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel 0)) = ⊥ := by
  apply le_antisymm
  · intro g hg
    apply zeroBaseEval_injective
    simpa only [map_zero] using (HolGerm.mem_maximalIdeal_iff g).mp hg
  · exact bot_le

/-- Actual relative Hadamard identifies the SAME normal-coordinate ideal with the original ambient maximal ideal. -/
theorem zeroTangentNormalIdeal_eq_maximalIdeal (d : ℕ) :
    normalIdeal 0 d = IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+d))) := by
  have h := baseMaximalIdeal_sup_normalIdeal 0 d
  have hb : originalBaseMaximalIdeal 0 d = ⊥ := by
    unfold originalBaseMaximalIdeal
    rw [zeroBaseMaximalIdeal_eq_bot,Ideal.map_bot]
  simpa only [hb,bot_sup_eq] using h

/-- Original complex coefficients become their SAME actual zero-dimensional constant germs. -/
def zeroBaseCoefficientEquiv (d k : ℕ) :
    (normalExponentIndex d (k+1) → ℂ) ≃ₗ[ℂ]
      (normalExponentIndex d (k+1) → HolGerm (ComplexModel 0)) :=
  LinearEquiv.piCongrRight (fun _ => zeroBaseComplexAlgEquiv.symm.toLinearEquiv)

/-- The ACTUAL original base jets have genuine distinct complex monomial coordinates. -/
def actualZeroTangentJetComplexEquiv (d k : ℕ) :
    let := normalExponentFintype d (k+1)
    (normalExponentIndex d (k+1) → ℂ) ≃ₗ[ℂ]
      (HolGerm (ComplexModel (0+d)) ⧸
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+d))) ^ (k+1)) := by
  let := tangentAlgebra 0 d
  let := normalExponentFintype d (k+1)
  let : IsScalarTower ℂ (HolGerm (ComplexModel 0)) (HolGerm (ComplexModel (0+d))) :=
    IsScalarTower.of_algHom (tangentPullback 0 d)
  exact (zeroBaseCoefficientEquiv d k).trans
    (((normalPowerLinearEquiv 0 d (k+1)).restrictScalars ℂ).trans
      (Ideal.quotientEquivAlgOfEq ℂ
        (congrArg (fun J : Ideal (HolGerm (ComplexModel (0+d))) => J ^ (k+1))
          (zeroTangentNormalIdeal_eq_maximalIdeal d))).toLinearEquiv)

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Every complex coordinate basis vector retains its SAME original whole monomial class. -/
theorem actualZeroTangentJetComplexEquiv_single (d k : ℕ) (α : normalExponentIndex d (k+1)) :
    let := normalExponentFintype d (k+1)
    actualZeroTangentJetComplexEquiv d k (Pi.single α 1) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+d))) ^ (k+1))
        (normalExponentMonomial 0 d α.val) := by
  classical
  let := tangentAlgebra 0 d
  let := normalExponentFintype d (k+1)
  let : IsScalarTower ℂ (HolGerm (ComplexModel 0)) (HolGerm (ComplexModel (0+d))) :=
    IsScalarTower.of_algHom (tangentPullback 0 d)
  have hc : zeroBaseCoefficientEquiv d k (Pi.single α 1) = Pi.single α 1 := by
    funext β
    by_cases h : β=α <;> simp [zeroBaseCoefficientEquiv,LinearEquiv.piCongrRight_apply,
      h]
  have hm := normalMonomialBasis_apply 0 d (k+1) α
  rw [normalMonomialBasis,Module.Basis.map_apply,Pi.basisFun_apply] at hm
  simp only [actualZeroTangentJetComplexEquiv,LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply,hc,hm,AlgEquiv.toLinearEquiv_apply,
    Ideal.quotientEquivAlgOfEq_mk]

/-- The retained option multiset and the actual slack multiplicity partition every original symbol. -/
theorem optionMultisetCard {A : Type*} [DecidableEq A] (s : Multiset (Option A)) :
    (s.filterMap id).card + s.count none = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    cases a <;> simp <;> omega

/-- Discarding then replacing the actual slack symbols recovers the WHOLE original multiset. -/
theorem optionMultisetReconstruction {A : Type*} [DecidableEq A] (s : Multiset (Option A)) :
    (s.filterMap id).map some + Multiset.replicate (s.count none) none = s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    cases a <;> simp [Multiset.replicate_succ,ih,Multiset.cons_add,Multiset.add_cons]

/-- The genuine normal exponent degree counts its actual multiplicity multiset. -/
theorem normalExponentDegree_eq_multisetCard (d : ℕ) (α : Fin d →₀ ℕ) :
    normalExponentDegree α = α.toMultiset.card := by
  classical
  rw [Finsupp.card_toMultiset]
  exact (α.sum_fintype (fun _ n => n) (fun _ => rfl)).symm

/-- The actual slack symbols add no retained original exponent. -/
theorem filterMap_none_replicate {A : Type*} (n : ℕ) :
    (Multiset.replicate n (none : Option A)).filterMap id = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [Multiset.replicate_succ,ih]

/-- Actual original exponents fill the same degree bound with genuine slack symbols. -/
def normalExponentToSym (d k : ℕ) (α : normalExponentIndex d (k+1)) :
    Sym (Option (Fin d)) k :=
  ⟨α.val.toMultiset.map some + Multiset.replicate (k-normalExponentDegree α.val) none,by
    simp only [Multiset.card_add,Multiset.card_map,Multiset.card_replicate]
    have h := α.property
    rw [normalExponentDegree_eq_multisetCard] at h ⊢
    omega⟩

/-- Discarding actual slack symbols produces the SAME original bounded exponent. -/
def normalExponentFromSym (d k : ℕ) (s : Sym (Option (Fin d)) k) :
    normalExponentIndex d (k+1) :=
  ⟨(s.val.filterMap id).toFinsupp,by
    rw [normalExponentDegree_eq_multisetCard,Multiset.toFinsupp_toMultiset]
    have h := optionMultisetCard s.val
    rw [s.property] at h
    omega⟩

/-- Every genuine original exponent is unchanged by the entire slack-symbol roundtrip. -/
theorem normalExponentFromSym_toSym (d k : ℕ) (α : normalExponentIndex d (k+1)) :
    normalExponentFromSym d k (normalExponentToSym d k α) = α := by
  apply Subtype.ext
  dsimp only [normalExponentFromSym,normalExponentToSym]
  rw [Multiset.filterMap_add,Multiset.filterMap_map,filterMap_none_replicate,add_zero]
  change (α.val.toMultiset.filterMap some).toFinsupp = α.val
  rw [Multiset.filterMap_some,Finsupp.toMultiset_toFinsupp]

/-- Every actual symmetric multiset keeps ALL its original symbols in the inverse roundtrip. -/
theorem normalExponentToSym_fromSym (d k : ℕ) (s : Sym (Option (Fin d)) k) :
    normalExponentToSym d k (normalExponentFromSym d k s) = s := by
  apply Subtype.ext
  dsimp only [normalExponentToSym,normalExponentFromSym]
  rw [Multiset.toFinsupp_toMultiset,normalExponentDegree_eq_multisetCard,Multiset.toFinsupp_toMultiset]
  have hs : k-(s.val.filterMap id).card = s.val.count none := by
    have h := optionMultisetCard s.val
    rw [s.property] at h
    omega
  rw [hs]
  exact optionMultisetReconstruction s.val

/-- The ORIGINAL bounded exponent index is genuinely equivalent to the finite symmetric power with slack. -/
def normalExponentSymEquiv (d k : ℕ) :
    normalExponentIndex d (k+1) ≃ Sym (Option (Fin d)) k where
  toFun := normalExponentToSym d k
  invFun := normalExponentFromSym d k
  left_inv := normalExponentFromSym_toSym d k
  right_inv := normalExponentToSym_fromSym d k

/-- Actual DISTINCT original monomials have the true tangent binomial cardinality. -/
theorem actualNormalExponentIndex_card (d k : ℕ) :
    let := normalExponentFintype d (k+1)
    Fintype.card (normalExponentIndex d (k+1)) = (d+k).choose d := by
  let := normalExponentFintype d (k+1)
  dsimp only
  rw [Fintype.card_congr (normalExponentSymEquiv d k),Sym.card_sym_eq_choose]
  simp only [Fintype.card_option,Fintype.card_fin]
  have h : d+1+k-1 = d+k := by omega
  rw [h]
  exact Nat.choose_symm_add.symm

/-- The genuine original complex base-jet dimension is EXACTLY the binomial tangent weight. -/
theorem actualBaseJetDimension (d k : ℕ) :
    Module.finrank ℂ
      (HolGerm (ComplexModel d) ⧸ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (k+1)) =
        (d+k).choose d := by
  let := normalExponentFintype d (k+1)
  have hd : Module.finrank ℂ
      (HolGerm (ComplexModel (0+d)) ⧸ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+d))) ^ (k+1)) =
        (d+k).choose d := by
    rw [← (actualZeroTangentJetComplexEquiv d k).finrank_eq,Module.finrank_fintype_fun_eq_card]
    exact actualNormalExponentIndex_card d k
  rw [Nat.zero_add] at hd
  exact hd

end
end Hironaka.HironakaRelativeNormalActualBaseJetDimension
