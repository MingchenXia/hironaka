/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalOriginalFiniteJetGenerators
import Hironaka.Analytic.FiniteGermIdealPullbackGenerators

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalCoherentTranslatedJets
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaIdealOperations OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalFiniteJetSplitting HironakaRelativeNormalOriginalFiniteJetGenerators
  FiniteGermIdealPullbackGenerators GermIdealPullbackCalculus RelativePrincipalizationSpan
  InvertibleIdealQuotient

/-- A genuine affine map of the original manifolds, not a map of arbitrary origin germs. -/
def actualAffineTranslation (n : ℕ) (a : ComplexModel n) (z : ComplexModel n) : ComplexModel n := a+z

theorem actualAffineTranslation_zero (n : ℕ) (a : ComplexModel n) : actualAffineTranslation n a 0 = a := add_zero a

theorem actualAffineTranslation_contMDiff (n : ℕ) (a : ComplexModel n) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualAffineTranslation n a) := by
  apply contMDiff_iff_contDiff.mpr
  exact contDiff_const.add contDiff_id

def actualTranslatedOriginalSheaf {n : ℕ} (I : GermIdeal n (ComplexModel n)) (a : ComplexModel n) :
    GermIdeal n (ComplexModel n) := GermIdeal.pullback (m := n) (actualAffineTranslation n a) I

theorem actualTranslatedOriginalSheaf_isCoherent {n : ℕ}
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) (a : ComplexModel n) :
    (actualTranslatedOriginalSheaf I a).IsCoherent :=
  isCoherent_pullback (actualAffineTranslation_contMDiff n a) hI

def actualAffineFunctionPullback (n : ℕ) (a : ComplexModel n) :
    (ComplexModel n → ℂ) →+* (ComplexModel n → ℂ) where
  toFun f := f ∘ actualAffineTranslation n a
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem actual_translated_function_holAt {n : ℕ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) {f : ComplexModel n → ℂ}
    (hf : MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) f U)
    {a : ComplexModel n} (ha : a ∈ U) : HolAt (f ∘ actualAffineTranslation n a) 0 := by
  have hg := holomorphicAt_of_mdifferentiableOn hU hf ha
  have hzero : HolomorphicAt n f (actualAffineTranslation n a 0) := by
    simpa only [actualAffineTranslation_zero] using hg
  exact (hzero.comp_contMDiff (Eventually.of_forall fun _ =>
    (actualAffineTranslation_contMDiff n a).contMDiffAt)).mono fun _ h => h.differentiableAt

private theorem actual_translated_sheaf_mem_iff {n N : ℕ}
    (I : GermIdeal n (ComplexModel n)) (S : Fin N → ComplexModel n → ℂ)
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hS : ∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (S i) U)
    (hgen : ∀ y ∈ U, ∀ f, I.mem y f ↔ IsInSpanAt (n := n) (· ∈ range S) y f)
    {a : ComplexModel n} (ha : a ∈ U) (f : ComplexModel n → ℂ) :
    (actualTranslatedOriginalSheaf I a).mem 0 f ↔
      IsInSpanAt (n := n) (· ∈ range fun i => S i ∘ actualAffineTranslation n a) 0 f := by
  apply mem_pullback_iff_of_finite_generation
    (Eventually.of_forall fun _ => (actualAffineTranslation_contMDiff n a).contMDiffAt)
  · intro i
    simpa only [actualAffineTranslation_zero] using holomorphicAt_of_mdifferentiableOn hU (hS i) ha
  · simpa only [actualAffineTranslation_zero] using hgen a ha

theorem exists_original_actual_translated_functions {n : ℕ}
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧
      ∃ (N : ℕ) (S : Fin N → ComplexModel n → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (S i) U) ∧
        (∀ a ∈ U, ∀ f, I.mem a f ↔ IsInSpanAt (n := n) (· ∈ range S) a f) ∧
        ∀ a ∈ U, ∀ i, HolAt (S i ∘ actualAffineTranslation n a) 0 := by
  obtain ⟨U,hU,h0,N,S,hS,hgen⟩ := hI 0
  exact ⟨U,hU,h0,N,S,hS,hgen,fun _ ha i => actual_translated_function_holAt hU (hS i) ha⟩

theorem actualTranslatedGenerator_raw {n : ℕ} (a : ComplexModel n)
    (f : ComplexModel n → ℂ) (hf : HolAt (f ∘ actualAffineTranslation n a) 0) :
    ((HolGerm.mk (f ∘ actualAffineTranslation n a) hf : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) = f ∘ actualAffineTranslation n a :=
  HolGerm.coe_mk _ _

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
private theorem actual_translated_origin_ideal_eq_span {n N : ℕ}
    (I : GermIdeal n (ComplexModel n)) (S : Fin N → ComplexModel n → ℂ)
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hS : ∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (S i) U)
    (hgen : ∀ y ∈ U, ∀ f, I.mem y f ↔ IsInSpanAt (n := n) (· ∈ range S) y f)
    {a : ComplexModel n} (ha : a ∈ U) (hhol : ∀ i, HolAt (S i ∘ actualAffineTranslation n a) 0) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a) =
      Ideal.span (range fun i => HolGerm.mk (S i ∘ actualAffineTranslation n a) (hhol i)) := by
  classical
  have hdict : ∀ (f : ComplexModel n → ℂ) (hf : HolAt f 0),
      (actualTranslatedOriginalSheaf I a).mem 0 f ↔
        HolGerm.mk f hf ∈ Ideal.span (range fun i => HolGerm.mk (S i ∘ actualAffineTranslation n a) (hhol i)) := by
    intro f hf
    rw [actual_translated_sheaf_mem_iff I S hU hS hgen ha f]
    constructor
    · intro h
      obtain ⟨_,c,hc,he⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp h
      exact (inSpanAt_zero_iff_mem_origin_span _ hhol hf).mp
        ⟨hf,c,fun i => (hc i).mono (fun _ hz => hz.differentiableAt),he⟩
    · intro h
      obtain ⟨hh,c,hc,he⟩ := (inSpanAt_zero_iff_mem_origin_span _ hhol hf).mpr h
      exact CoherentIdealColon.isInSpanAt_range_iff.mpr
        ⟨hh.mono (fun _ hz => hz.mdifferentiableAt),c,
          fun i => (hc i).mono (fun _ hz => hz.mdifferentiableAt),he⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    exact (hdict f hf).mp hIf
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    apply Ideal.subset_span
    refine ⟨S i ∘ actualAffineTranslation n a,hhol i,?_,rfl⟩
    apply (actual_translated_sheaf_mem_iff I S hU hS hgen ha _).mpr
    exact CoherentIdealColon.isInSpanAt_range_self
      (fun j => (hhol j).mono (fun _ hz => hz.mdifferentiableAt)) i

theorem exists_original_actual_translated_ideal_dictionary {n : ℕ}
    (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧
      ∃ (N : ℕ) (S : Fin N → ComplexModel n → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (S i) U) ∧
        (∀ a ∈ U, ∀ f, I.mem a f ↔ IsInSpanAt (n := n) (· ∈ range S) a f) ∧
        ∃ hhol : ∀ a ∈ U, ∀ i, HolAt (S i ∘ actualAffineTranslation n a) 0,
          (∀ a (ha : a ∈ U), originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a) =
            Ideal.span (range fun i => HolGerm.mk (S i ∘ actualAffineTranslation n a) (hhol a ha i))) ∧
          ∀ a ∈ U, ∀ f, (actualTranslatedOriginalSheaf I a).mem 0 f ↔
            IsInSpanAt (n := n) (· ∈ range fun i => S i ∘ actualAffineTranslation n a) 0 f := by
  obtain ⟨U,hU,h0,N,S,hS,hgen,hhol⟩ := exists_original_actual_translated_functions I hI
  exact ⟨U,hU,h0,N,S,hS,hgen,hhol,
    fun _ ha => actual_translated_origin_ideal_eq_span I S hU hS hgen ha (hhol _ ha),
    fun _ ha f => actual_translated_sheaf_mem_iff I S hU hS hgen ha f⟩

private theorem actual_translated_ideal_jet_span (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) {N : ℕ}
    (G : Fin N → HolGerm (ComplexModel (d+t))) (hgen : I = Ideal.span (range G)) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    LinearMap.range (actualIdealJetMap d t I q) =
      Submodule.span (HolGerm (ComplexModel d)) (range (finiteGeneratorColumn d t q G)) := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  apply le_antisymm
  · rintro y ⟨a,rfl⟩
    have ha : a.val ∈ Ideal.span (range G) := by rw [← hgen]; exact a.property
    obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
    change Ideal.Quotient.mk (normalIdeal d t ^ q) a.val ∈ _
    rw [← hc,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_mul,← (normalMonomialBasis d t q).sum_repr (Ideal.Quotient.mk (normalIdeal d t ^ q) (c i)),Finset.sum_mul]
    apply Submodule.sum_mem
    intro α _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,α),rfl⟩)
  · apply Submodule.span_le.mpr
    rintro y ⟨k,rfl⟩
    exact finiteGeneratorColumn_mem_original_image d t q I G
      (fun i => by rw [hgen]; exact Ideal.subset_span ⟨i,rfl⟩) k

/-- Conclusion only: the entire actual translated ORIGINAL jet image, never an input certificate. -/
def actualTranslatedJetImageDictionary (d t : ℕ) (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (U : Set (ComplexModel (d+t))) (N : ℕ) (S : Fin N → ComplexModel (d+t) → ℂ)
    (hhol : ∀ a ∈ U, ∀ i, HolAt (S i ∘ actualAffineTranslation (d+t) a) 0) : Prop :=
  letI := tangentAlgebra d t
  ∀ a (ha : a ∈ U), ∀ q : ℕ,
    letI := normalExponentFintype t q
    let G := fun i => HolGerm.mk (S i ∘ actualAffineTranslation (d+t) a) (hhol a ha i)
    (∀ k, finiteGeneratorColumn d t q G k ∈ LinearMap.range
      (actualIdealJetMap d t (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a)) q)) ∧
    LinearMap.range (actualIdealJetMap d t (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a)) q) =
      Submodule.span (HolGerm (ComplexModel d)) (range (finiteGeneratorColumn d t q G)) ∧
    ∀ y : ambientNormalJet d t q,
      y ∈ LinearMap.range (actualIdealJetMap d t (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a)) q) ↔
        ∃ c : Fin N × normalExponentIndex t q → HolGerm (ComplexModel d),
          ∑ k, c k • finiteGeneratorColumn d t q G k = y

theorem exists_original_coherent_actual_translated_jets (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
      ∃ (N : ℕ) (S : Fin N → ComplexModel (d+t) → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (S i) U) ∧
        (∀ a ∈ U, ∀ f, I.mem a f ↔ IsInSpanAt (n := d+t) (· ∈ range S) a f) ∧
        ∃ hhol : ∀ a ∈ U, ∀ i, HolAt (S i ∘ actualAffineTranslation (d+t) a) 0,
          (∀ a (ha : a ∈ U), originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a) =
            Ideal.span (range fun i => HolGerm.mk (S i ∘ actualAffineTranslation (d+t) a) (hhol a ha i))) ∧
          (∀ a ∈ U, ∀ f, (actualTranslatedOriginalSheaf I a).mem 0 f ↔
            IsInSpanAt (n := d+t) (· ∈ range fun i => S i ∘ actualAffineTranslation (d+t) a) 0 f) ∧
          actualTranslatedJetImageDictionary d t I U N S hhol := by
  classical
  let := tangentAlgebra d t
  obtain ⟨U,hU,h0,N,S,hS,hgen,hhol,hideal,hmem⟩ := exists_original_actual_translated_ideal_dictionary I hI
  refine ⟨U,hU,h0,N,S,hS,hgen,hhol,hideal,hmem,?_⟩
  intro a ha q
  let := normalExponentFintype t q
  let G := fun i => HolGerm.mk (S i ∘ actualAffineTranslation (d+t) a) (hhol a ha i)
  have himage := actual_translated_ideal_jet_span d t q
    (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a)) G (hideal a ha)
  have hG : ∀ i, G i ∈ originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a) := by
    intro i
    rw [hideal a ha]
    exact Ideal.subset_span ⟨i,rfl⟩
  refine ⟨finiteGeneratorColumn_mem_original_image d t q _ G hG,himage,?_⟩
  intro y
  rw [himage]
  exact Submodule.mem_span_range_iff_exists_fun (HolGerm (ComplexModel d))

end
end Hironaka.HironakaRelativeNormalCoherentTranslatedJets
