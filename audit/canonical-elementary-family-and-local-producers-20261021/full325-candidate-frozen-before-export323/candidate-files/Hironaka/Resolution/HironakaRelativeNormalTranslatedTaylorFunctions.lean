/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalCoherentTranslatedJets
import Hironaka.Resolution.HironakaRelativeNormalTaylorCoefficients

/-!
Actual whole affine derivative functions and whole nearby original Taylor germs.
Complete Mathematics.tex was written first. Formal/native registration pending root.
Nearby projector-image identification, whole Rees/normal cone and G8 remain OPEN.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff Nat
namespace Hironaka.HironakaRelativeNormalTranslatedTaylorFunctions
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HolomorphicTaylorTail HironakaRelativeNormalIdeal HironakaRelativeNormalTaylorCoefficients
  HironakaRelativeNormalCoherentTranslatedJets
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalDeformationInitialRelations

def actualTranslatedSourceOpen {n : ℕ} (U : Set (ComplexModel n)) (a : ComplexModel n) :
    Set (ComplexModel n) := actualAffineTranslation n a ⁻¹' U

theorem actualTranslatedSourceOpen_isOpen {n : ℕ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (a : ComplexModel n) : IsOpen (actualTranslatedSourceOpen U a) :=
  hU.preimage (actualAffineTranslation_contMDiff n a).continuous

theorem actualTranslatedSourceOpen_mem_nhds {n : ℕ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) {a : ComplexModel n} (ha : a ∈ U) :
    actualTranslatedSourceOpen U a ∈ 𝓝 (0 : ComplexModel n) :=
  (actualTranslatedSourceOpen_isOpen hU a).mem_nhds (by
    change actualAffineTranslation n a 0 ∈ U
    simpa only [actualAffineTranslation_zero] using ha)

theorem iterDeriv_actualAffineTranslation {n : ℕ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) {f : ComplexModel n → ℂ} (hf : DifferentiableOn ℂ f U)
    (a : ComplexModel n) :
    ∀ L : List (ComplexModel n), ∀ z : ComplexModel n,
      actualAffineTranslation n a z ∈ U →
      iterDeriv L (f ∘ actualAffineTranslation n a) z =
        iterDeriv L f (actualAffineTranslation n a z)
  | [], _, _ => rfl
  | v :: L, z, hz => by
    have he : iterDeriv L (f ∘ actualAffineTranslation n a) =ᶠ[𝓝 z]
        (iterDeriv L f ∘ actualAffineTranslation n a) := by
      filter_upwards [(actualTranslatedSourceOpen_isOpen hU a).mem_nhds hz] with w hw
      exact iterDeriv_actualAffineTranslation hU hf a L w hw
    have hd := (differentiableOn_iterDeriv hf hU L _ hz).differentiableAt (hU.mem_nhds hz)
    simp only [iterDeriv_cons, dirDeriv]
    rw [he.fderiv_eq, fderiv_comp z hd ((differentiableAt_const a).add differentiableAt_id)]
    simp only [ContinuousLinearMap.comp_apply]
    change (fderiv ℂ (iterDeriv L f) (a+z))
      ((fderiv ℂ (fun w : ComplexModel n => a+w) z) v) =
        (fderiv ℂ (iterDeriv L f) (a+z)) v
    rw [fderiv_const_add]
    change (fderiv ℂ (iterDeriv L f) (a+z))
      ((fderiv ℂ (id : ComplexModel n → ComplexModel n) z) v) =
        (fderiv ℂ (iterDeriv L f) (a+z)) v
    rw [fderiv_id]
    rfl

theorem iterDeriv_actualAffineTranslation_eventually {n : ℕ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) {f : ComplexModel n → ℂ} (hf : DifferentiableOn ℂ f U)
    {a : ComplexModel n} (ha : a ∈ U) (L : List (ComplexModel n)) :
    iterDeriv L (f ∘ actualAffineTranslation n a) =ᶠ[𝓝 0]
      (iterDeriv L f ∘ actualAffineTranslation n a) := by
  filter_upwards [actualTranslatedSourceOpen_mem_nhds hU ha] with z hz
  exact iterDeriv_actualAffineTranslation hU hf a L z hz

theorem iterDeriv_actualAffineTranslation_differentiableOn {n : ℕ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) {f : ComplexModel n → ℂ} (hf : DifferentiableOn ℂ f U)
    (a : ComplexModel n) (L : List (ComplexModel n)) :
    DifferentiableOn ℂ (iterDeriv L (f ∘ actualAffineTranslation n a))
      (actualTranslatedSourceOpen U a) := by
  apply differentiableOn_iterDeriv ?_ (actualTranslatedSourceOpen_isOpen hU a) L
  intro z hz
  exact ((hf _ hz).differentiableAt (hU.mem_nhds hz)).comp z
    ((differentiableAt_const a).add differentiableAt_id) |>.differentiableWithinAt

/-- The genuine normalized whole base FUNCTION, without taking any point value. -/
def actualTranslatedNormalTaylorFunction (d t : ℕ) (L : List (Fin t))
    (f : ComplexModel (d+t) → ℂ) (a : ComplexModel (d+t)) (u : ComplexModel d) : ℂ :=
  (L.length.factorial : ℂ)⁻¹ *
    iterDeriv (L.map (normalVector d t)) f (a+tangentInclusion d t u)

theorem actualTranslatedNormalTaylorFunction_holAt (d t : ℕ) (L : List (Fin t))
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    {f : ComplexModel (d+t) → ℂ} (hf : DifferentiableOn ℂ f U)
    {a : ComplexModel (d+t)} (ha : a ∈ U) :
    HolAt (actualTranslatedNormalTaylorFunction d t L f a) 0 := by
  have ht : Tendsto (tangentInclusion d t) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)
  filter_upwards [ht.eventually (actualTranslatedSourceOpen_mem_nhds hU ha)] with u hu
  have hd := (differentiableOn_iterDeriv hf hU (L.map (normalVector d t)) _
    hu).differentiableAt (hU.mem_nhds hu)
  exact (hd.comp u ((differentiableAt_const a).add (tangentInclusion d t).differentiableAt)).const_mul _

theorem relativeTaylorCoefficient_actualTranslated_function (d t : ℕ) (L : List (Fin t))
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    {f : ComplexModel (d+t) → ℂ} (hf : DifferentiableOn ℂ f U)
    {a : ComplexModel (d+t)} (ha : a ∈ U)
    (hfa : HolAt (f ∘ actualAffineTranslation (d+t) a) 0) :
    relativeTaylorCoefficient d t L (HolGerm.mk (f ∘ actualAffineTranslation (d+t) a) hfa) =
      HolGerm.mk (actualTranslatedNormalTaylorFunction d t L f a)
        (actualTranslatedNormalTaylorFunction_holAt d t L hU hf ha) := by
  unfold relativeTaylorCoefficient planeTrace
  rw [iteratedDerivativeGerm_mk, compAlgHom_mk, Algebra.smul_def]
  have hd : HolAt
      (iterDeriv (L.map (normalVector d t)) (f ∘ actualAffineTranslation (d+t) a)
        ∘ tangentInclusion d t) 0 :=
    holomorphic_comp _ (Eventually.of_forall fun _ => (tangentInclusion d t).differentiableAt)
      (map_zero _) (eventually_holomorphic_iterDeriv hfa _)
  have hm := eventually_differentiableAt_mul
    (eventually_differentiableAt_const (L.length.factorial : ℂ)⁻¹) hd
  change HolGerm.mk
      (fun u => (L.length.factorial : ℂ)⁻¹ *
        iterDeriv (L.map (normalVector d t))
          (f ∘ actualAffineTranslation (d+t) a) (tangentInclusion d t u)) hm =
    HolGerm.mk (actualTranslatedNormalTaylorFunction d t L f a) _
  apply HolGerm.mk_eq_mk_iff.mpr
  have ht : Tendsto (tangentInclusion d t) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)
  filter_upwards [ht.eventually (iterDeriv_actualAffineTranslation_eventually hU hf ha
    (L.map (normalVector d t)))] with u hu
  exact congrArg (fun c : ℂ => (L.length.factorial : ℂ)⁻¹ * c) hu

/-- The literal finite tuple of the genuine actual normalized coefficient FUNCTIONS. -/
def actualTranslatedTaylorFunctionTuple (d t q : ℕ)
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    {f : ComplexModel (d+t) → ℂ} (hf : DifferentiableOn ℂ f U)
    {a : ComplexModel (d+t)} (ha : a ∈ U) :
    monomialIndex t q → HolGerm (ComplexModel d) :=
  fun w => HolGerm.mk (actualTranslatedNormalTaylorFunction d t (List.ofFn w.2) f a)
    (actualTranslatedNormalTaylorFunction_holAt d t _ hU hf ha)

theorem normalTaylorCoefficients_actualTranslated_function (d t q : ℕ)
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    {f : ComplexModel (d+t) → ℂ} (hf : DifferentiableOn ℂ f U)
    {a : ComplexModel (d+t)} (ha : a ∈ U)
    (hfa : HolAt (f ∘ actualAffineTranslation (d+t) a) 0) :
    letI := tangentAlgebra d t
    normalTaylorCoefficients d t q (HolGerm.mk (f ∘ actualAffineTranslation (d+t) a) hfa) =
      actualTranslatedTaylorFunctionTuple d t q hU hf ha := by
  let := tangentAlgebra d t
  funext w
  exact relativeTaylorCoefficient_actualTranslated_function d t _ hU hf ha hfa

theorem actualTranslatedTaylorFunctionTuple_eq_iff_quotient (d t q : ℕ)
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    {f g : ComplexModel (d+t) → ℂ} (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g U) {a : ComplexModel (d+t)} (ha : a ∈ U)
    (hfa : HolAt (f ∘ actualAffineTranslation (d+t) a) 0)
    (hga : HolAt (g ∘ actualAffineTranslation (d+t) a) 0) :
    actualTranslatedTaylorFunctionTuple d t q hU hf ha =
      actualTranslatedTaylorFunctionTuple d t q hU hg ha ↔
    Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (f ∘ actualAffineTranslation (d+t) a) hfa) =
      Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (g ∘ actualAffineTranslation (d+t) a) hga) := by
  let := tangentAlgebra d t
  rw [← normalTaylorCoefficients_actualTranslated_function d t q hU hf ha hfa,
    ← normalTaylorCoefficients_actualTranslated_function d t q hU hg ha hga]
  have he :
      normalTaylorCoefficients d t q (HolGerm.mk (f ∘ actualAffineTranslation (d+t) a) hfa) =
        normalTaylorCoefficients d t q (HolGerm.mk (g ∘ actualAffineTranslation (d+t) a) hga) ↔
      HolGerm.mk (f ∘ actualAffineTranslation (d+t) a) hfa -
        HolGerm.mk (g ∘ actualAffineTranslation (d+t) a) hga ∈ normalIdeal d t ^ q :=
    normalTaylorCoefficients_eq_iff d t q _ _
  exact he.trans Ideal.Quotient.eq.symm

/-- Only the original coherent sheaf supplies SAME nearby functions, original images and whole Taylor dictionaries. -/
theorem exists_original_coherent_translated_Taylor_functions (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ (U : Set (ComplexModel (d+t))) (hU : IsOpen U), 0 ∈ U ∧
      ∃ (N : ℕ) (S : Fin N → ComplexModel (d+t) → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (S i) U) ∧
        (∀ a ∈ U, ∀ f, I.mem a f ↔ IsInSpanAt (n := d+t) (· ∈ range S) a f) ∧
        ∃ hhol : ∀ a ∈ U, ∀ i, HolAt (S i ∘ actualAffineTranslation (d+t) a) 0,
          (∀ a (ha : a ∈ U), originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a) =
            Ideal.span (range fun i => HolGerm.mk (S i ∘ actualAffineTranslation (d+t) a) (hhol a ha i))) ∧
          (∀ a ∈ U, ∀ f, (actualTranslatedOriginalSheaf I a).mem 0 f ↔
            IsInSpanAt (n := d+t) (· ∈ range fun i => S i ∘ actualAffineTranslation (d+t) a) 0 f) ∧
          actualTranslatedJetImageDictionary d t I U N S hhol ∧
          ∃ hdiff : ∀ i, DifferentiableOn ℂ (S i) U,
            (∀ a (ha : a ∈ U), ∀ i L,
              relativeTaylorCoefficient d t L (HolGerm.mk (S i ∘ actualAffineTranslation (d+t) a) (hhol a ha i)) =
                HolGerm.mk (actualTranslatedNormalTaylorFunction d t L (S i) a)
                  (actualTranslatedNormalTaylorFunction_holAt d t L hU (hdiff i) ha)) ∧
            ∀ a (ha : a ∈ U), ∀ i q,
              normalTaylorCoefficients d t q (HolGerm.mk (S i ∘ actualAffineTranslation (d+t) a) (hhol a ha i)) =
                actualTranslatedTaylorFunctionTuple d t q hU (hdiff i) ha := by
  let := tangentAlgebra d t
  obtain ⟨U,hU,h0,N,S,hS,hgen,hhol,hideal,hmem,himage⟩ :=
    exists_original_coherent_actual_translated_jets d t I hI
  have hdiff : ∀ i, DifferentiableOn ℂ (S i) U :=
    fun i => mdifferentiableOn_iff_differentiableOn.mp (hS i)
  refine ⟨U,hU,h0,N,S,hS,hgen,hhol,hideal,hmem,himage,hdiff,?_,?_⟩
  · exact fun a ha i L => relativeTaylorCoefficient_actualTranslated_function d t L hU (hdiff i) ha (hhol a ha i)
  · exact fun a ha i q => normalTaylorCoefficients_actualTranslated_function d t q hU (hdiff i) ha (hhol a ha i)

end
end Hironaka.HironakaRelativeNormalTranslatedTaylorFunctions
