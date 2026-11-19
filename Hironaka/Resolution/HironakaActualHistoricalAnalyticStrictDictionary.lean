import Hironaka.Resolution.HironakaActualHistoricalNormalizedLeadingFrames
import Hironaka.Resolution.HironakaActualHistoricalFreePivotSaturation
import Hironaka.Resolution.HironakaActualStrictPullbackSaturation
import Hironaka.Resolution.HironakaActualFormalIdealContraction

/-! Genuine analytic normalization of the SAME entire historical family
equals the TRUE geometric strict-transform ideal, from actual marked
orders before any target HS comparison. Saturation is proved internally. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalAnalyticStrictDictionary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualHistoricalWholeJetFrames
  HironakaActualHistoricalFormalSupportedDivision HironakaActualCauchyMonomialDivision
  HironakaActualOriginalFormalHSTransfer HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualHistoricalFreePivotSaturation
  HironakaActualHistoricalNormalizedLeadingFrames HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalDeformationInitialRelations HironakaActualStrictPullbackSaturation

variable {n k : ℕ}

private theorem unshifted_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j=>HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem mem_unshifted_extension_iff
    (J : Ideal (HolGerm (ComplexModel n))) (F : HolGerm (ComplexModel n)) :
    F∈J ↔ actualUnshiftedTaylorAlgHom n F∈Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom J := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop:=
    ∀(I : Ideal (HolGerm (ComplexModel m)))(g : HolGerm (ComplexModel m)),
      g∈I ↔ f g∈Ideal.map f.toRingHom I
  exact unshifted_property n P (mem_original_ideal_iff_formal_extension n) J F

/-- Whole Taylor contraction turns DERIVED formal free-pivot saturation
into actual analytic saturation of the SAME finite family ideal. -/
theorem actual_historical_analytic_free_pivot_power_iff
    (w : Fin k → CoordinateWord n) (N : Fin k → HolGerm (ComplexModel n))
    (hmarked : ∀j,actualUnshiftedTaylorAlgHom n (N j)∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun j=>actualUnshiftedTaylorAlgHom n (N j)) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun j=>actualUnshiftedTaylorAlgHom n (N j)))
    (e : Fin n) (hFree : ∀j,wordExponent (w j) e=0)
    (d : ℕ) (F : HolGerm (ComplexModel n)) :
    (coordinateGerm e)^d*F∈Ideal.span (range N) ↔ F∈Ideal.span (range N) := by
  have hMap : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range N))=
      Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (N j)):=by
    rw [Ideal.map_span,←range_comp]
    rfl
  constructor
  · intro hI
    have hm:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hI
    change actualUnshiftedTaylorAlgHom n ((coordinateGerm e)^d*F)∈
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range N)) at hm
    rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate,hMap] at hm
    have hF:=(historical_ideal_free_pivot_power_iff w _ hmarked hwhole hSupported e hFree d _).mp hm
    apply (mem_unshifted_extension_iff _ F).mpr
    rwa [hMap]
  · intro hI
    exact Ideal.mul_mem_left _ _ hI

/-- Actual source geometry and actual normalized POINT MARKS construct
analytic SAME-member quotients and identify their ENTIRE span with the
TRUE geometric strict ideal. No target HS/strict dictionary is a premise. -/
theorem exists_actual_historical_analytic_strict_generators_of_marks
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IsComplexAnalyticSubset (n:=d+t) W)
    (w : Fin k → CoordinateWord (d+t)) (Γ : Fin k → HolGerm (ComplexModel (d+t)))
    (hspan : Ideal.span (range Γ)=originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))
    (B : Set (Fin (d+t))) (hHeads : ∀i q,q∉B → wordExponent (w i) q=0)
    (hBA : B⊆actualTangentCentreVariables d t\{j.natAdd d})
    (hCentre : ∀i,Γ i∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^
      normalExponentDegree (wordExponent (w i)))
    (hmarked : ∀i,actualUnshiftedTaylorAlgHom (d+t) (Γ i)∈
      genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)))
    (hTargetMarked : ∀i,actualNormalizedFormalMember (actualTangentCentreVariables d t) (j.natAdd d)
      (⟨j,rfl⟩ : j.natAdd d∈actualTangentCentreVariables d t) b
      (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom (d+t) (Γ i))
      (actualTaylor_mem_coordinateCentre_pow _ _ _ (hCentre i))∈
        genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i))) :
    ∃N : Fin k → HolGerm (ComplexModel (d+t)),
      (∀i,(coordinateGerm (j.natAdd d))^normalExponentDegree (wordExponent (w i))*N i=
        actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (Γ i)) ∧
      (∀i,actualUnshiftedTaylorAlgHom (d+t) (N i)=
        actualNormalizedFormalMember (actualTangentCentreVariables d t) (j.natAdd d)
          (⟨j,rfl⟩ : j.natAdd d∈actualTangentCentreVariables d t) b
          (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom (d+t) (Γ i))
          (actualTaylor_mem_coordinateCentre_pow _ _ _ (hCentre i))) ∧
      originalCoherentOriginIdeal (vanishingIdeal (n:=d+t)
        (strictTransform (d+t)
          (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W))=
        Ideal.span (range N) := by
  let A:=actualTangentCentreVariables d t
  let e:=j.natAdd d
  have he : e∈A:=⟨j,rfl⟩
  let μ:=fun i=>normalExponentDegree (wordExponent (w i))
  let g:=fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)
  have hFormalCentre (i) : g i∈actualFormalCoordinateIdeal (d+t) A^μ i:=
    actualTaylor_mem_coordinateCentre_pow A (μ i) (Γ i) (hCentre i)
  choose N hProduct hTaylor using fun i=>exists_actualAnalyticBlowup_quotient A e he b (μ i) (Γ i) (hCentre i)
  have hFramesSupported:=actual_normalized_whole_supported_division_of_marks
    w g hmarked hwhole hSupported A B e he b hHeads hBA hFormalCentre hTargetMarked
  have hNmarked : ∀i,actualUnshiftedTaylorAlgHom (d+t) (N i)∈
      genuineFormalVariables (d+t)^μ i:=by
    simpa only [hTaylor] using hTargetMarked
  have hNwhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (N i)) q):=by
    simpa only [hTaylor] using hFramesSupported.1
  have hNSupported : HistoricalWholeSupportedDivision w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (N i)):=by
    simpa only [hTaylor] using hFramesSupported.2
  have hFree (i : Fin k) : wordExponent (w i) e=0:=
    hHeads i e (fun heB=>(hBA heB).2 rfl)
  let a:=coordinateGerm e
  let I:=originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W)
  let K:=Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom I
  let J:=Ideal.span (range N)
  have hSat (q : ℕ) (F : HolGerm (ComplexModel (d+t))) : a^q*F∈J ↔ F∈J:=
    actual_historical_analytic_free_pivot_power_iff w N hNmarked hNwhole hNSupported e hFree q F
  have hK : K=Ideal.span (range fun i=>a^(μ i)*N i):=by
    change Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
      (originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))=_
    rw [←hspan,Ideal.map_span]
    apply congrArg Ideal.span
    ext F
    constructor
    · rintro ⟨G,⟨i,rfl⟩,rfl⟩
      exact ⟨i,hProduct i⟩
    · rintro ⟨i,rfl⟩
      exact ⟨Γ i,⟨i,rfl⟩,(hProduct i).symm⟩
  have hKJ : K≤J:=by
    rw [hK]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
  let M:=Finset.univ.sup μ
  have hμ (i : Fin k) : μ i≤M:=Finset.le_sup (Finset.mem_univ i)
  have hIntoK (F : HolGerm (ComplexModel (d+t))) (hF : F∈J) : a^M*F∈K:=by
    obtain ⟨c,hc⟩:=Ideal.mem_span_range_iff_exists_fun.mp hF
    rw [←hc,Finset.mul_sum]
    apply Ideal.sum_mem
    intro i _
    have hGen : a^(μ i)*N i∈K:=by rw [hK];exact Ideal.subset_span ⟨i,rfl⟩
    have hm:=Ideal.mul_mem_left K (a^(M-μ i)*c i) hGen
    have hPow : a^M=a^(M-μ i)*a^(μ i):=by rw [←pow_add,Nat.sub_add_cancel (hμ i)]
    have heq : (a^(M-μ i)*c i)*(a^(μ i)*N i)=a^M*(c i*N i):=by rw [hPow];ring
    exact heq ▸ hm
  refine ⟨N,hProduct,hTaylor,?_⟩
  ext F
  rw [mem_original_analytic_strict_ideal_iff_exists_coordinate_power d t ht j b W hW F]
  constructor
  · rintro ⟨q,hq⟩
    exact (hSat q F).mp (hKJ hq)
  · intro hF
    exact ⟨M,hIntoK F hF⟩

end
end Hironaka.HironakaActualHistoricalAnalyticStrictDictionary
