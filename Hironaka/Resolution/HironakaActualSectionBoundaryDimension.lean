import Hironaka.Resolution.HironakaSmoothSubmersionCanonicalValueDimensionShift
import Hironaka.Resolution.HironakaActualSectionInitialValues
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionBoundaryDimension
noncomputable section
open CanonicalCentres MonomialInvariant MonomialCase
open HironakaSmoothSubmersionCanonicalValueDimensionShift

def sameIndexMap (t : ℕ) : (q : ℕ) → ValTy q → ValTy q
  | 0 => id
  | q+1 => generalDimensionMap t (stepDimensionMap (sameIndexMap t q))

theorem strictMono_sameIndexMap (t : ℕ) : ∀ q, StrictMono (sameIndexMap t q)
  | 0 => strictMono_id
  | q+1 => strictMono_generalDimensionMap t
      (strictMono_stepDimensionMap (strictMono_sameIndexMap t q))

def sameIndexEmbedding (t q : ℕ) : ValTy q ↪o ValTy q :=
  OrderEmbedding.ofStrictMono (sameIndexMap t q) (strictMono_sameIndexMap t q)

theorem sameIndexMap_comparisons (t q : ℕ) (v w : ValTy q) :
    (sameIndexMap t q v < sameIndexMap t q w ↔ v<w) ∧
    (sameIndexMap t q v ≤ sameIndexMap t q w ↔ v≤w) ∧
    (sameIndexMap t q v = sameIndexMap t q w ↔ v=w) :=
  ⟨(strictMono_sameIndexMap t q).lt_iff_lt,
    (strictMono_sameIndexMap t q).le_iff_le,
    (strictMono_sameIndexMap t q).injective.eq_iff⟩

theorem sameIndexMap_maximum_iff {α : Type*} (t q : ℕ) (f : α→ValTy q) (x : α) :
    (∀ y, sameIndexMap t q (f y) ≤ sameIndexMap t q (f x)) ↔ ∀ y, f y ≤ f x := by
  exact forall_congr' (fun _ => (strictMono_sameIndexMap t q).le_iff_le)

open Hironaka.HolomorphicIdealSheaves DivisorExponentAlong
open HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
open HironakaActualOpenZeroSectionDifferentials HironakaActualSectionInitialValues
variable {n : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}

theorem isDivNearAlong_section_iff (A H : Set U) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g, J.mem z g → HolomorphicAt (n+1) g z) (e : ℕ) (x : U) :
    IsDivNearAlong (n+1) (liftedCarrier A) J (projection U ⁻¹' H) e (zeroSection U x) ↔
    IsDivNearAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) H e x := by
  have hps : ∀ y : U, projection U (zeroSection U y)=y := by
    intro y
    apply Subtype.ext
    exact tangentProjection_tangentInclusion n 1 y.val
  constructor
  · intro h
    have hh:= (zeroSection_contMDiff U).continuous.continuousAt.eventually h
    filter_upwards [hh] with y hy hyA hyH
    have hsA : zeroSection U y∈liftedCarrier A := by
      change projection U (zeroSection U y)∈A ∧ _
      exact ⟨by rwa [hps],by change actualJointNormalProjection n 1 (tangentInclusion n 1 y)=0; simp⟩
    have hc:=hy hsA (by simpa only [Set.mem_preimage,hps] using hyH)
    rw [source_cosupport_eq_lifted A J hJ e] at hc
    simpa only [hps] using hc.1
  · intro h
    have hp : Tendsto (projection U) (𝓝 (zeroSection U x)) (𝓝 x) := by
      simpa only [hps] using (projection_contMDiff U).continuous.tendsto (zeroSection U x)
    filter_upwards [hp.eventually h] with z hz hzA hzH
    rw [source_cosupport_eq_lifted A J hJ e]
    exact ⟨hz hzA.1 hzH,hzA.2⟩

theorem divExpAlong_section_eq (A H : Set U) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g, J.mem z g → HolomorphicAt (n+1) g z) (x : U) :
    divExpAlong (n+1) (liftedCarrier A) J (projection U ⁻¹' H) (zeroSection U x)=
    divExpAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) H x := by
  classical
  have hP : (fun e => IsDivNearAlong (n+1) (liftedCarrier A) J
      (projection U ⁻¹' H) e (zeroSection U x))=
      fun e => IsDivNearAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) H e x :=
    funext fun e => propext (isDivNearAlong_section_iff A H J hJ e x)
  unfold divExpAlong
  change (if h : ∃e, ¬(fun e => IsDivNearAlong (n+1) (liftedCarrier A) J
      (projection U ⁻¹' H) e (zeroSection U x)) (e+1) then Nat.find h else 0)=_
  rw [hP]

open MonomialCaseAlong

theorem expDataAlong_section_eq (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g, J.mem z g → HolomorphicAt (n+1) g z) (x : U) :
    expDataAlong (n+1) (liftedCarrier A) J (E.map (projection U ⁻¹' ·)) (zeroSection U x)=
    expDataAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) E x := by
  funext i
  unfold expDataAlong
  by_cases hi : i<E.length
  · have hi' : i<(E.map (projection U ⁻¹' ·)).length := by simpa using hi
    rw [dif_pos hi',dif_pos hi]
    have he : (E.map (projection U ⁻¹' ·)).get ⟨i,hi'⟩=projection U ⁻¹' E.get ⟨i,hi⟩ := by simp
    rw [he]
    exact divExpAlong_section_eq A _ J hJ x
  · have hi' : ¬i<(E.map (projection U ⁻¹' ·)).length := by simpa using hi
    rw [dif_neg hi',dif_neg hi]

theorem memberIdx_section_eq (E : List (Set U)) (x : U) :
    memberIdx (E.map (projection U ⁻¹' ·)) (zeroSection U x)=memberIdx E x := by
  have hps : projection U (zeroSection U x)=x := by
    apply Subtype.ext
    exact tangentProjection_tangentInclusion n 1 x
  ext i
  rw [mem_memberIdx,mem_memberIdx]
  constructor
  · rintro ⟨hi,hx⟩
    exact ⟨by simpa using hi,by simpa [hps] using hx⟩
  · rintro ⟨hi,hx⟩
    exact ⟨by simpa using hi,by simpa [hps] using hx⟩

theorem gammaAlong_section_dimension_shift (A : Set U) (E : List (Set U))
    (hE : NormalCrossings.IsSNCDivisor n E) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g, J.mem z g → HolomorphicAt (n+1) g z) (d : ℕ) (x : U) :
    gammaAlong (n+1) (liftedCarrier A) J (E.map (projection U ⁻¹' ·)) d (zeroSection U x)=
    dimensionValue 1 (gammaAlong n A (GermIdeal.pullback (m := n) (zeroSection U) J) E d x) := by
  unfold gammaAlong
  rw [memberIdx_section_eq,expDataAlong_section_eq A E J hJ x]
  exact inv_dimension_shift n 1 _ _ d (card_memberIdx_le E hE x)

end
end Hironaka.HironakaActualSectionBoundaryDimension
