import Hironaka.Resolution.HironakaActualCoefficientDivisorExponentGap
import Hironaka.Resolution.HironakaActualOriginalStrictContactWeightedOrder

/-! Native direct high-cut/finite-Nat.find normalized exponents of ORIGINAL lower records.
Blueprint FIRST. Generic arithmetic is PRIVATE and assumes no future history.
The public ordinary-source endpoint derives EVERY cut/gap/coherence hypothesis. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualOriginalContactBoundaryExponentScaling
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder DivisorExponentAlong MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedIdealAlong HomogenizedGlueingTower
  ContactStageKept CoefficientIdeal CoefficientIdealRestriction ContactIndependenceAlong GermIdealPullbackCalculus
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec HironakaActualOriginalHistoricalBarWeightedThreshold
  HironakaActualCoefficientDivisorExponentGap HironakaActualOriginalStrictContactWeightedOrder
  StepOneValue StepOneValueMasked CompanionRebase CompanionReductionAlong CompanionOpen
  NonmonomialOrderLocal NonmonomialOrderTail HironakaEmbeddedAnalytic

variable {n : ℕ} {X : CMfd.{u} n}

private theorem hol {Y : CMfd.{u} n} {I : GermIdeal n Y} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x := fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem all_near_of_no_failure (N : Set X) (I : GermIdeal n X)
    (hI : ∀x f,I.mem x f→HolomorphicAt n f x) (H : Set X) (x : X)
    (hNo : ¬∃r,¬IsDivNearAlong n N I H (r+1) x) :
    ∀q,IsDivNearAlong n N I H q x := by
  intro q
  cases q with
  | zero=>exact isDivNearAlong_zero hI x
  | succ q=>by_contra hBad;exact hNo ⟨q,hBad⟩

private theorem unbounded_transfer (N : Set X) (A B : GermIdeal n X)
    (hA : ∀x f,A.mem x f→HolomorphicAt n f x) (hB : ∀x f,B.mem x f→HolomorphicAt n f x)
    (f g : ℕ) (hg : 1≤g)
    (hCuts : ∀y∈N,∀a b : ℕ,0<b→b≤a→
      ((((f*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N A y) ↔
        (((g*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N B y)))
    (H : Set X) (x : X) (hAll : ∀q,IsDivNearAlong n N A H q x) :
    ∀q,IsDivNearAlong n N B H q x := by
  intro q
  have hHigh:=hAll (f*(q+1))
  filter_upwards [hHigh] with y hy hyN hyH
  have hAord : ((f*(q+1) : ℕ) : ℕ∞)≤GermIdealOrder.order n N A y:=
    (le_order_iff (hA y)).mpr (hy hyN hyH).2
  have hBcut:=(hCuts y hyN (q+1) 1 (by omega) (by omega)).mp
    (by simpa only [Nat.cast_one,one_mul] using hAord)
  have hBord : ((g*(q+1) : ℕ) : ℕ∞)≤GermIdealOrder.order n N B y:=by
    simpa only [Nat.cast_one,one_mul] using hBcut
  have hq : q≤g*(q+1):=by
    have hMul:=Nat.mul_le_mul_right (q+1) hg
    simp only [Nat.one_mul] at hMul
    omega
  exact ⟨hyN,(le_order_iff (hB y)).mp
    ((show (q : ℕ∞)≤((g*(q+1) : ℕ) : ℕ∞) by exact_mod_cast hq).trans hBord)⟩

private theorem finite_transfer (N : Set X) (A B : GermIdeal n X)
    (hA : ∀x f,A.mem x f→HolomorphicAt n f x) (hB : ∀x f,B.mem x f→HolomorphicAt n f x)
    (f g : ℕ) (hf : 1≤f)
    (hCuts : ∀y∈N,∀a b : ℕ,0<b→b≤a→
      ((((f*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N A y) ↔
        (((g*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N B y)))
    (H : Set X) (x : X) (hEx : ∃r,¬IsDivNearAlong n N A H (r+1) x) :
    ∃r,¬IsDivNearAlong n N B H (r+1) x := by
  by_contra hNoB
  have hAllB:=all_near_of_no_failure N B hB H x hNoB
  have hAllA:=unbounded_transfer N B A hB hA g f hf
    (fun y hy a b hb hba=>(hCuts y hy a b hb hba).symm) H x hAllB
  obtain ⟨r,hr⟩:=hEx
  exact hr (hAllA (r+1))

private theorem not_near_successor_of_finite (N : Set X) (I : GermIdeal n X) (H : Set X) (x : X)
    (hEx : ∃r,¬IsDivNearAlong n N I H (r+1) x) :
    ¬IsDivNearAlong n N I H (divExpAlong n N I H x+1) x := by
  unfold divExpAlong
  rw [dif_pos hEx]
  exact Nat.find_spec hEx

private theorem zero_transfer (N : Set X) (A B : GermIdeal n X)
    (hA : ∀x f,A.mem x f→HolomorphicAt n f x) (hB : ∀x f,B.mem x f→HolomorphicAt n f x)
    (f g : ℕ) (hf : 1≤f)
    (hCuts : ∀y∈N,∀a b : ℕ,0<b→b≤a→
      ((((f*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N A y) ↔
        (((g*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N B y)))
    (H : Set X) (x : X) (hExA : ∃r,¬IsDivNearAlong n N A H (r+1) x)
    (hGapB : divExpAlong n N B H x=0 ∨ g≤divExpAlong n N B H x)
    (hZeroA : divExpAlong n N A H x=0) : divExpAlong n N B H x=0 := by
  by_contra hNonzeroB
  have hge:=hGapB.resolve_left hNonzeroB
  have hBHigh:=(isDivNearAlong_divExpAlong (N:=N) (H:=H) hB x).mono hge
  have hAHigh : IsDivNearAlong n N A H f x:=by
    filter_upwards [hBHigh] with y hy hyN hyH
    have hBord : (g : ℕ∞)≤GermIdealOrder.order n N B y:=
      (le_order_iff (hB y)).mpr (hy hyN hyH).2
    have hAcut:=(hCuts y hyN 1 1 (by omega) le_rfl).mpr
      (by simpa only [Nat.mul_one,Nat.cast_one,one_mul] using hBord)
    exact ⟨hyN,(le_order_iff (hA y)).mp
      (by simpa only [Nat.mul_one,Nat.cast_one,one_mul] using hAcut)⟩
  have hNot:=not_near_successor_of_finite N A H x hExA
  rw [hZeroA,Nat.zero_add] at hNot
  exact hNot (hAHigh.mono hf)

private theorem bounded_failure_point (N : Set X) (I : GermIdeal n X)
    (hI : ∀x f,I.mem x f→HolomorphicAt n f x) (H : Set X) (x : X) (r : ℕ)
    (hNot : ¬IsDivNearAlong n N I H (r+1) x)
    {P : X→Prop} (hNear : ∀ᶠ y in 𝓝 x,P y) :
    ∃y,y∈N ∧ y∈H ∧ GermIdealOrder.order n N I y≤(r : ℕ∞) ∧ P y := by
  unfold IsDivNearAlong at hNot
  rw [Filter.not_eventually] at hNot
  have hFreq : ∃ᶠ y in 𝓝 x,y∈N ∧ y∈H ∧ y∉cosupport n N I (r+1):=
    hNot.mono fun y hy=>by
      obtain ⟨hyN,hy⟩:=Classical.not_imp.mp hy
      obtain ⟨hyH,hyCos⟩:=Classical.not_imp.mp hy
      exact ⟨hyN,hyH,hyCos⟩
  obtain ⟨y,⟨hyN,hyH,hyCos⟩,hyP⟩:=(hFreq.and_eventually hNear).exists
  have hNotOrder : ¬((r+1 : ℕ) : ℕ∞)≤GermIdealOrder.order n N I y:=
    fun h=>hyCos ⟨hyN,(le_order_iff (hI y)).mp h⟩
  have hBound : GermIdealOrder.order n N I y≤(r : ℕ∞):=
    ENat.lt_natCast_add_one_iff.mp (lt_of_not_ge (by
      simpa only [Nat.cast_add,Nat.cast_one] using hNotOrder))
  exact ⟨y,hyN,hyH,hBound,hyP⟩

private theorem positive_cross_le (N : Set X) (A B : GermIdeal n X)
    (hA : ∀x f,A.mem x f→HolomorphicAt n f x) (hB : ∀x f,B.mem x f→HolomorphicAt n f x)
    (f g : ℕ) (hf : 1≤f)
    (hCuts : ∀y∈N,∀a b : ℕ,0<b→b≤a→
      ((((f*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N A y) ↔
        (((g*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N B y)))
    (H : Set X) (x : X) (hf_le : f≤divExpAlong n N A H x)
    (hExB : ∃r,¬IsDivNearAlong n N B H (r+1) x) :
    g*divExpAlong n N A H x≤f*divExpAlong n N B H x := by
  let rA:=divExpAlong n N A H x
  let rB:=divExpAlong n N B H x
  have hNotB:=not_near_successor_of_finite N B H x hExB
  have hDivA:=isDivNearAlong_divExpAlong (N:=N) (H:=H) hA x
  obtain ⟨y,hyN,hyH,hBbound,hyDiv⟩:=bounded_failure_point N B hB H x rB hNotB hDivA
  have hAord : (rA : ℕ∞)≤GermIdealOrder.order n N A y:=
    (le_order_iff (hA y)).mpr (hyDiv hyN hyH).2
  have hScaled : ((f*rA : ℕ) : ℕ∞)≤(f : ℕ∞)*GermIdealOrder.order n N A y:=by
    rw [Nat.cast_mul]
    gcongr
  have hPeer:=(hCuts y hyN rA f (by omega) hf_le).mp hScaled
  have hUpper : (f : ℕ∞)*GermIdealOrder.order n N B y≤((f*rB : ℕ) : ℕ∞):=by
    rw [Nat.cast_mul]
    gcongr
  have hNat : ((g*rA : ℕ) : ℕ∞)≤((f*rB : ℕ) : ℕ∞):=hPeer.trans hUpper
  exact_mod_cast hNat

private theorem native_exponent_scaling (N : Set X) (A B : GermIdeal n X)
    (hA : ∀x f,A.mem x f→HolomorphicAt n f x) (hB : ∀x f,B.mem x f→HolomorphicAt n f x)
    (f g : ℕ) (hf : 1≤f) (hg : 1≤g)
    (hCuts : ∀y∈N,∀a b : ℕ,0<b→b≤a→
      ((((f*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N A y) ↔
        (((g*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N B y)))
    (H : Set X) (x : X)
    (hGapA : divExpAlong n N A H x=0 ∨ f≤divExpAlong n N A H x)
    (hGapB : divExpAlong n N B H x=0 ∨ g≤divExpAlong n N B H x) :
    g*divExpAlong n N A H x=f*divExpAlong n N B H x := by
  have hSym : ∀y∈N,∀a b : ℕ,0<b→b≤a→
      ((((g*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N B y) ↔
        (((f*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n N A y)):=
    fun y hy a b hb hba=>(hCuts y hy a b hb hba).symm
  by_cases hExA : ∃r,¬IsDivNearAlong n N A H (r+1) x
  · have hExB:=finite_transfer N A B hA hB f g hf hCuts H x hExA
    by_cases hZeroA : divExpAlong n N A H x=0
    · have hZeroB:=zero_transfer N A B hA hB f g hf hCuts H x hExA hGapB hZeroA
      simp only [hZeroA,hZeroB,Nat.mul_zero]
    · have hNonzeroB : divExpAlong n N B H x≠0:=by
        intro hZeroB
        exact hZeroA (zero_transfer N B A hB hA g f hg hSym H x hExB hGapA hZeroB)
      exact Nat.le_antisymm
        (positive_cross_le N A B hA hB f g hf hCuts H x (hGapA.resolve_left hZeroA) hExB)
        (positive_cross_le N B A hB hA g f hg hSym H x (hGapB.resolve_left hNonzeroB) hExA)
  · have hNoB : ¬∃r,¬IsDivNearAlong n N B H (r+1) x:=
      fun hExB=>hExA (finite_transfer N B A hB hA g f hg hSym H x hExB)
    unfold divExpAlong
    rw [dif_neg hExA,dif_neg hNoB]
    simp only [Nat.mul_zero]

private theorem contact_ideal_coherent {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (w : X→ℂ) (U : TopologicalSpace.Opens Y) :
    (contactMarkedKept M w T U).ideal.IsCoherent := by
  have hBarT:=(original_bar_weighted_history M hM T hT).2.1
  exact isCoherent_pullback contMDiff_subtype_val
    (isCoherent_coeffMarkedAlong hBarT.isWellFormed.isCoherent hBarT.isWellFormed.isClosedSubmanifold_N)

/- All cuts/gaps in this composition are derived by1116/135 in the PUBLIC endpoint. -/
private theorem stage_exponent_scaling {kJ kK : ℕ} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hTJ : IsGeoTestTower J T) (hTK : IsGeoTestTower K T)
    (w : X→ℂ) (U : TopologicalSpace.Opens Y)
    (hN : (contactMarkedKept J w T U).N=(contactMarkedKept K w T U).N)
    (hCuts : ∀y : U,y.val∈strictAlong T (K.N∩{y | w y=0})→∀a b : ℕ,0<b→b≤a→
      (((((contactMarkedKept J w T U).d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*
        GermIdealOrder.order n (contactMarkedKept J w T U).N (contactMarkedKept J w T U).ideal y) ↔
      ((((contactMarkedKept K w T U).d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*
        GermIdealOrder.order n (contactMarkedKept K w T U).N (contactMarkedKept K w T U).ideal y))) :
    let RJ:=contactMarkedKept J w T U
    let RK:=contactMarkedKept K w T U
    ∀(H : Set U)(x : U),
      RK.d*divExpAlong n RJ.N RJ.ideal H x=RJ.d*divExpAlong n RK.N RK.ideal H x := by
  let RJ:=contactMarkedKept J w T U
  let RK:=contactMarkedKept K w T U
  have hCJ:=contact_ideal_coherent J hJ T hTJ w U
  have hCK:=contact_ideal_coherent K hK T hTK w U
  have hPosJ : 1≤RJ.d:=one_le_coeffMarkedAlong_d (geoTransformAlong (coeffMarkedAlong (homMarkedAlong J)) T)
  have hPosK : 1≤RK.d:=one_le_coeffMarkedAlong_d (geoTransformAlong (coeffMarkedAlong (homMarkedAlong K)) T)
  have hGapJ:=(original_contact_divisor_exponent_gap J hJ T hTJ w U).2.2.2
  have hGapK:=(original_contact_divisor_exponent_gap K hK T hTK w U).2.2.2
  have hPointCuts : ∀y∈RJ.N,∀a b : ℕ,0<b→b≤a→
      ((((RJ.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RJ.N RJ.ideal y) ↔
       (((RK.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RJ.N RK.ideal y)):=by
    intro y hy a b hb hba
    have hyK : y∈RK.N:=by rw [←hN];exact hy
    have hAt:=hCuts y (show y.val∈strictAlong T (K.N∩{y | w y=0}) from hyK) a b hb hba
    rwa [←hN] at hAt
  dsimp only
  intro H x
  have hGapK' : divExpAlong n RJ.N RK.ideal H x=0 ∨ RK.d≤divExpAlong n RJ.N RK.ideal H x:=by
    rw [hN]
    exact hGapK H x
  rw [←hN]
  exact native_exponent_scaling (X:=CMfd.of (n:=n) U) RJ.N RJ.ideal RK.ideal
    (hol (Y:=CMfd.of (n:=n) U) hCJ) (hol (Y:=CMfd.of (n:=n) U) hCK)
    RJ.d RK.d hPosJ hPosK hPointCuts H x (hGapJ H x) hGapK'

/-- Ordinary ORIGINAL inputs derive ALL actual cuts/gaps before normalized lower exponents. -/
theorem original_lower_contact_boundary_exponent_scaling {A : CMfd.{0} n}
    (hn : 0<n) (Q : MarkedIdeal n A) {k : ℕ} (hQ : IsInvDomain k Q)
    (hN : Q.N=univ) (hE : Q.E=[]) (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set A) (hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W) (a : A) (ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower A A) a,
      let V:=maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V:=⟨a,hm⟩
      let μ:=nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=companionOf n P μ
      let K:=companionOf n B (e*μ)
      ∃hxU : x∈U,
        IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧ J.d=μ ∧ K.d=e*μ ∧
        (⟨x,hxU⟩ : U)∈J.cosupp ∧ (⟨x,hxU⟩ : U)∈K.cosupp ∧
        ∀z₀∈K.cosupp,∃hOpen : IsOpen (tangentChoice K z₀).1,
          let U₀ : TopologicalSpace.Opens (CMfd.of (n:=n) U):=⟨(tangentChoice K z₀).1,hOpen⟩
          ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J T→
            IsGeoTestTower K T ∧
            let Z:=openPreimage T U₀
            let RJ:=contactMarkedKept J (tangentChoice K z₀).2 T Z
            let RK:=contactMarkedKept K (tangentChoice K z₀).2 T Z
            RJ.N=RK.N ∧ RJ.E=RK.E ∧
            RJ.d=(Finset.range ((Finset.range μ).prod (fun j=>μ-j))).prod
              (fun j=>(Finset.range μ).prod (fun j=>μ-j)-j) ∧
            RK.d=(Finset.range ((Finset.range (e*μ)).prod (fun j=>e*μ-j))).prod
              (fun j=>(Finset.range (e*μ)).prod (fun j=>e*μ-j)-j) ∧
            RJ.E.length=T.length ∧ RK.E.length=T.length ∧
            ∀(H : Set Z)(x : Z),
              RK.d*divExpAlong n RJ.N RJ.ideal H x=RJ.d*divExpAlong n RK.N RK.ideal H x := by
  obtain ⟨hm,hxU,hJ,hK,hJd,hKd,hzJ,hzK,hContacts⟩:=
    original_lower_common_contact_history_thresholds hn Q hQ hN hE hMax W hW hSing a ha
  refine ⟨hm,hxU,hJ,hK,hJd,hKd,hzJ,hzK,?_⟩
  intro z₀ hz₀
  obtain ⟨hOpen,hHist⟩:=hContacts z₀ hz₀
  refine ⟨hOpen,?_⟩
  dsimp only
  intro Y T hTJ
  obtain ⟨hTK,hNR,hER,hdJR,hdKR,hLenJR,hLenKR,hCuts⟩:=hHist T hTJ
  exact ⟨hTK,hNR,hER,hdJR,hdKR,hLenJR,hLenKR,
    stage_exponent_scaling _ _ hJ hK T hTJ hTK _ _ hNR hCuts⟩

end
end Hironaka.HironakaActualOriginalContactBoundaryExponentScaling
