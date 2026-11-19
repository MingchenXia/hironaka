import Hironaka.Resolution.HironakaActualNormalZeroFormalSaturation
import Hironaka.Resolution.HironakaActualRelativeNormalJetDivision
import Hironaka.Resolution.HironakaActualAnalyticStrictGenerators
import Hironaka.Resolution.HironakaActualUnshiftedInitialHSTransfer

/-!
# Whole analytic exceptional saturation for the SAME inherited zero-chart family

Actual analytic quotients are chosen from the literal source normal marks before
any target-order assumption. Genuine whole Taylor contraction preserves the
source family, identifies the entire normalized-member ideal, and reflects the
internally produced exceptional regularity. No analytic syzygy, target diagram,
HS equality, radicality or saturation certificate is an input.

Source-only draft. No kernel acceptance is asserted.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalZeroAnalyticSaturation
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalTaylor HironakaActualFormalIdealContraction
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
  HironakaActualOriginalFormalHSTransfer HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalStrictGenerators
  HironakaActualReducedBasisDivision HironakaActualRelativeStandardnessInheritedDivision
  HironakaActualRelativeNormalJetDivision HironakaActualAnalyticBlowupTaylor
  HironakaActualAnalyticStrictGenerators HironakaActualUnshiftedInitialHSTransfer
  HironakaActualNormalZeroOwnerConverse HironakaActualNormalZeroFormalSaturation

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

/-- Every WHOLE actual analytic ideal contracts from its genuine unshifted Taylor extension. -/
theorem mem_analytic_ideal_iff_actualUnshifted_extension (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (g : HolGerm (ComplexModel n)) :
    g ∈ I ↔ actualUnshiftedTaylorAlgHom n g ∈ Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (L : Ideal (HolGerm (ComplexModel m))) (g : HolGerm (ComplexModel m)),
      g ∈ L ↔ f g ∈ Ideal.map f.toRingHom L
  exact unshiftedTaylor_property n P (mem_original_ideal_iff_formal_extension n) I g

/-- Genuine unshifted Taylor extension is injective on entire analytic ideals. -/
theorem actualUnshifted_ideal_extension_injective (n : ℕ) :
    Function.Injective (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom) := by
  intro I J h
  ext g
  rw [mem_analytic_ideal_iff_actualUnshifted_extension n I g,
    mem_analytic_ideal_iff_actualUnshifted_extension n J g, h]

/-- Every genuine analytic maximal power has its literal formal variable-power extension. -/
theorem map_actualUnshifted_maximal_pow (n q : ℕ) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) = genuineFormalVariables n ^ q := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ q : ℕ, Ideal.map f.toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel m)) ^ q) =
      genuineFormalVariables n ^ q
  exact unshiftedTaylor_property n P (map_original_maximal_pow_eq_formal_variables_pow n) q

/-- The literal source Taylor ideal; the whole analytic ideal is retained. -/
def analyticZeroTaylorIdeal (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :
    Ideal (MvPowerSeries (Fin n) ℂ) := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I

/-- SAME analytic inherited germs, supplied with their actual source membership,
viewed as the specified genuine monic full formal family. -/
def analyticZeroMonicFamily (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hmem : ∀ a, G.germs a ∈ I) : ActualMonicVertexFamily MonomialOrder.degLex (analyticZeroTaylorIdeal n I) :=
  { series := fun a => actualUnshiftedTaylorAlgHom n (G.germs a)
    mem := fun a => Ideal.mem_map_of_mem _ (hmem a)
    monic := G.monic
    lower := G.lower }

/-- The actual analytic normalized members are selected ONCE from the source
normal marks. Neither target marked orders nor HS data enter this definition. -/
def sameAnalyticZeroNormalizedVertex (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
    HolGerm (ComplexModel n) :=
  Classical.choose (exists_actualAnalyticBlowup_quotient (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
    (fun _ => 0) (normalExponentDegree a.val) (G.germs a) (hpower a))

/-- The SAME analytic quotient has its genuine exact exceptional product. -/
theorem sameAnalyticZeroNormalizedVertex_product (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
    (coordinateGerm e)^(normalExponentDegree a.val) * sameAnalyticZeroNormalizedVertex n I G e hpower a =
      actualAnalyticBlowupPullback (Set.Ici e) e (fun _ => 0) (G.germs a) :=
  (Classical.choose_spec (exists_actualAnalyticBlowup_quotient (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
    (fun _ => 0) (normalExponentDegree a.val) (G.germs a) (hpower a))).1

private theorem sameAnalyticZeroFormalMark (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
    actualUnshiftedTaylorAlgHom n (G.germs a) ∈
      actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val :=
  actualTaylor_mem_coordinateCentre_pow (n := n) (Set.Ici e)
    (normalExponentDegree a.val) (G.germs a) (hpower a)

/-- Its literal Taylor series is the actual formal normalized SAME member. -/
theorem actualTaylor_sameAnalyticZeroNormalizedVertex (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
    actualUnshiftedTaylorAlgHom n (sameAnalyticZeroNormalizedVertex n I G e hpower a) =
      actualNormalizedFormalMember (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0)
        (normalExponentDegree a.val) (actualUnshiftedTaylorAlgHom n (G.germs a))
        (sameAnalyticZeroFormalMark n I G e hpower a) := by
  apply actualNormalizedFormalMember_unique
  have ht := congrArg (actualUnshiftedTaylorAlgHom n)
    (sameAnalyticZeroNormalizedVertex_product n I G e hpower a)
  rw [map_mul, map_pow, actualUnshiftedTaylor_coordinate] at ht
  exact ht.trans (DFunLike.congr_fun
    (actualTaylor_analyticBlowupPullback (Set.Ici e) e (fun _ => 0)) (G.germs a))

/-- The finite analytic target ideal retains exactly these chosen inherited quotients. -/
def sameAnalyticZeroNormalizedIdeal (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val) :
    Ideal (HolGerm (ComplexModel n)) := Ideal.span (Set.range (sameAnalyticZeroNormalizedVertex n I G e hpower))

/-- Genuine whole source generation follows by whole Taylor contraction. No
analytic owner-division or independently chosen canonical family is needed. -/
theorem analytic_ideal_eq_span_same_inherited_family (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I) :
    Ideal.span (Set.range G.germs) = I := by
  apply actualUnshifted_ideal_extension_injective n
  rw [Ideal.map_span, ← Set.range_comp]
  exact ideal_eq_span_same_monic_family (analyticZeroTaylorIdeal n I) (analyticZeroMonicFamily n I G hmem)

/-- The entire Taylor extension of the SAME analytic quotient ideal is exactly
the actual whole formal strict ideal, without target orders or HS assumptions. -/
theorem map_sameAnalyticZeroNormalizedIdeal (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (sameAnalyticZeroNormalizedIdeal n I G e hpower) =
      actualFormalStrictTransform (analyticZeroTaylorIdeal n I) (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _ => 0) := by
  let B := analyticZeroMonicFamily n I G hmem
  have hp (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val :=
    actualTaylor_mem_coordinateCentre_pow (Set.Ici e) _ (G.germs a) (hpower a)
  rw [actual_normal_zero_strict_eq_same_monic_span (analyticZeroTaylorIdeal n I) B e hp,
    sameAnalyticZeroNormalizedIdeal, Ideal.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext a
  exact actualTaylor_sameAnalyticZeroNormalizedVertex n I G e hpower a

/-- The WHOLE analytic normalized-original-member ideal equals the SAME finite
inherited span. This is independent of target orders and all HS equalities. -/
theorem actualAnalyticNormalizedMemberIdeal_eq_same_zero_span (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val) :
    actualAnalyticNormalizedMemberIdeal I (Set.Ici e) e (fun _ => 0) =
      sameAnalyticZeroNormalizedIdeal n I G e hpower := by
  apply le_antisymm
  · intro g hg
    apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ g).mpr
    rw [map_sameAnalyticZeroNormalizedIdeal n I G hmem e hpower]
    exact map_actualAnalyticNormalizedMemberIdeal_le_formalStrictTransform I (Set.Ici e) e
      (Set.mem_Ici.mpr le_rfl) (fun _ => 0) (Ideal.mem_map_of_mem _ hg)
  · apply Ideal.span_le.mpr
    rintro g ⟨a, rfl⟩
    exact Ideal.subset_span ⟨normalExponentDegree a.val, G.germs a, hmem a, hpower a,
      sameAnalyticZeroNormalizedVertex_product n I G e hpower a⟩

/-- Genuine analytic marked orders internally yield exceptional cancellation for
the same entire normalized ideal, at every power including zero. -/
theorem coordinate_pow_mul_mem_same_zero_ideal_iff_of_marked_orders
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticZeroNormalizedVertex n I G e hpower a ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val)
    (q : ℕ) (g : HolGerm (ComplexModel n)) :
    (coordinateGerm e)^q * g ∈ sameAnalyticZeroNormalizedIdeal n I G e hpower ↔
      g ∈ sameAnalyticZeroNormalizedIdeal n I G e hpower := by
  let B := analyticZeroMonicFamily n I G hmem
  have hp (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val :=
    actualTaylor_mem_coordinateCentre_pow (Set.Ici e) _ (G.germs a) (hpower a)
  have ho (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      sameMonicZeroNormalizedVertex (analyticZeroTaylorIdeal n I) B e hp a ∈
        genuineFormalVariables n ^ normalExponentDegree a.val := by
    have h := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom (horder a)
    change actualUnshiftedTaylorAlgHom n (sameAnalyticZeroNormalizedVertex n I G e hpower a) ∈
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val) at h
    rw [map_actualUnshifted_maximal_pow, actualTaylor_sameAnalyticZeroNormalizedVertex] at h
    exact h
  constructor
  · intro hg
    apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ g).mpr
    rw [map_sameAnalyticZeroNormalizedIdeal n I G hmem e hpower]
    apply (actual_normal_zero_Xpow_mul_mem_strict_iff_of_marked_orders
      (analyticZeroTaylorIdeal n I) B e hp ho q (actualUnshiftedTaylorAlgHom n g)).mp
    have ht := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hg
    change actualUnshiftedTaylorAlgHom n ((coordinateGerm e)^q * g) ∈
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (sameAnalyticZeroNormalizedIdeal n I G e hpower) at ht
    rw [map_mul, map_pow, actualUnshiftedTaylor_coordinate,
      map_sameAnalyticZeroNormalizedIdeal n I G hmem e hpower] at ht
    exact ht
  · exact Ideal.mul_mem_left _ _

/-- Every actual analytic HS value follows from marked orders of the SAME
inherited normalized family. No target HS or diagram certificate is input. -/
theorem hilbertSamuelValue_same_zero_ideal_eq_of_marked_orders
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticZeroNormalizedVertex n I G e hpower a ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val)
    (ℓ : ℕ) :
    hilbertSamuelValue (sameAnalyticZeroNormalizedIdeal n I G e hpower) ℓ = hilbertSamuelValue I ℓ := by
  let B := analyticZeroMonicFamily n I G hmem
  have hp (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici e) ^ normalExponentDegree a.val :=
    actualTaylor_mem_coordinateCentre_pow (Set.Ici e) _ (G.germs a) (hpower a)
  have ho (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      sameMonicZeroNormalizedVertex (analyticZeroTaylorIdeal n I) B e hp a ∈
        genuineFormalVariables n ^ normalExponentDegree a.val := by
    have h := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom (horder a)
    change actualUnshiftedTaylorAlgHom n (sameAnalyticZeroNormalizedVertex n I G e hpower a) ∈
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val) at h
    rw [map_actualUnshifted_maximal_pow, actualTaylor_sameAnalyticZeroNormalizedVertex] at h
    exact h
  rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    map_sameAnalyticZeroNormalizedIdeal n I G hmem e hpower]
  exact (actual_normal_zero_strict_diagram_and_hs_of_inherited_marked_orders
    (analyticZeroTaylorIdeal n I) (analyticZeroTaylorIdeal n I)
    (⟨B.series, B.monic, B.lower⟩ : InheritedMonicFamily MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
    rfl B.mem e hp ho).2.2 ℓ

/-- One finite common power, WHOLE actual analytic saturation, and every genuine
analytic HS value are produced internally from the natural marked orders. -/
theorem exists_same_zero_analytic_fixed_colon_and_hs_of_marked_orders
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (e : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici e) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticZeroNormalizedVertex n I G e hpower a ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val) :
    ∃ M : ℕ,
      (∀ g ∈ sameAnalyticZeroNormalizedIdeal n I G e hpower,
        (coordinateGerm e)^M * g ∈ Ideal.map
          (actualAnalyticBlowupPullback (Set.Ici e) e (fun _ => 0)).toRingHom I) ∧
      sameAnalyticZeroNormalizedIdeal n I G e hpower =
        (Ideal.map (actualAnalyticBlowupPullback (Set.Ici e) e (fun _ => 0)).toRingHom I).colon {(coordinateGerm e)^M} ∧
      (∀ g : HolGerm (ComplexModel n), g ∈ sameAnalyticZeroNormalizedIdeal n I G e hpower ↔
        ∃ q : ℕ, (coordinateGerm e)^q * g ∈ Ideal.map
          (actualAnalyticBlowupPullback (Set.Ici e) e (fun _ => 0)).toRingHom I) ∧
      (∀ ℓ : ℕ, hilbertSamuelValue (sameAnalyticZeroNormalizedIdeal n I G e hpower) ℓ = hilbertSamuelValue I ℓ) := by
  let N := sameAnalyticZeroNormalizedIdeal n I G e hpower
  let T := Ideal.map (actualAnalyticBlowupPullback (Set.Ici e) e (fun _ => 0)).toRingHom I
  let H := sameAnalyticZeroNormalizedVertex n I G e hpower
  have hprod (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      (coordinateGerm e)^(normalExponentDegree a.val) * H a ∈ T := by
    change (coordinateGerm e)^(normalExponentDegree a.val) *
      sameAnalyticZeroNormalizedVertex n I G e hpower a ∈ T
    rw [sameAnalyticZeroNormalizedVertex_product]
    exact Ideal.mem_map_of_mem _ (hmem a)
  have hT : T ≤ N := by
    change Ideal.map (actualAnalyticBlowupPullback (Set.Ici e) e (fun _ => 0)).toRingHom I ≤ N
    rw [← analytic_ideal_eq_span_same_inherited_family n I G hmem, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro g ⟨f, ⟨a, rfl⟩, rfl⟩
    change actualAnalyticBlowupPullback (Set.Ici e) e (fun _ => 0) (G.germs a) ∈ N
    rw [← sameAnalyticZeroNormalizedVertex_product n I G e hpower a]
    exact N.mul_mem_left _ (Ideal.subset_span ⟨a, rfl⟩)
  have hreg (g : HolGerm (ComplexModel n)) (hg : coordinateGerm e * g ∈ N) : g ∈ N := by
    apply (coordinate_pow_mul_mem_same_zero_ideal_iff_of_marked_orders n I G hmem e hpower horder 1 g).mp
    simpa only [pow_one] using hg
  obtain ⟨M, _hM, hbound, hc, hs⟩ := exists_fixed_power_colon_of_finite_products T N (coordinateGerm e)
    (fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) => normalExponentDegree a.val)
    H rfl hT hprod hreg
  exact ⟨M, hbound, hc, hs, hilbertSamuelValue_same_zero_ideal_eq_of_marked_orders n I G hmem e hpower horder⟩

end
end Hironaka.HironakaActualNormalZeroAnalyticSaturation
