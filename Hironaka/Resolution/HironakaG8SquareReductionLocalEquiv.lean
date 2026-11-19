import Hironaka.Resolution.HironakaG8EqualWeightNativeThresholds
import Hironaka.Resolution.HironakaG8LocalPower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8SquareReductionLocalEquiv
noncomputable section

open scoped ProductComplexManifold

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings ProductComplexManifold HomogenizedGlueingTower GermIdealOrder IdealWeightPowers
  RelativePrincipalizationSpan OrderMultiplicativity GermOrderProduct OrderTaylor CompanionReduction IdealOrderArithmetic
  HironakaSharpOriginalProductTraceOrder ResolutionInvariantSpec HironakaG8LocalHistory
  HironakaG8LocalStable HironakaActualProjectionTestRecord HironakaG8MixedEquiv
  InvertibleIdealQuotient RestrictedIdealExtension ResolutionDriver

/-- An exact cubic reduction recovers the cosupport of a square-mark
record even when the square-generator ideal is strictly smaller than
the whole square ideal. -/
theorem square_reduction_cosupport {n : ℕ} {X : CMfd.{0} n}
    (I J : GermIdeal n X) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hn : ∀ x ∈ (univ : Set X), DivisorExponentAlong.IsNonzeroAlongAt univ I x)
    (hRed : I.mul J = idealPow I 3) (d : ℕ) :
    cosupport n univ I d = cosupport n univ J (d*2) := by
  ext x
  let r := ordinaryTraceOrder (X := X) univ I x
  have hOrder := ordinaryTraceOrder_cosupport_iff (X := X) isClosedSubmanifold_univ hI hn (mem_univ x)
  have hr : x ∈ cosupport n univ I r := (hOrder r).mpr le_rfl
  have hnr : x ∉ cosupport n univ I (r+1) := fun h => Nat.not_succ_le_self r ((hOrder (r+1)).mp h)
  have hHolI := fun x g h => GermIdeal.IsCoherent.holomorphicAt_mem hI (x := x) (g := g) h
  have hHolJ := fun x g h => GermIdeal.IsCoherent.holomorphicAt_mem hJ (x := x) (g := g) h
  constructor
  · intro hx
    have hle := (hOrder d).mp hx
    have hc : x ∈ cosupport n univ (I.mul J) (r*3) := by
      rw [hRed, cosupport_idealPow_mul_eq hHolI (by decide : 1 ≤ 3)]
      exact hr
    have hOut := mem_cosupport_of_mem_cosupport_mul hHolI hHolJ (by omega : r ≤ r*3) hc hnr
    exact cosupport_anti (by omega : d*2 ≤ r*3-r) hOut
  · intro hx
    apply (hOrder d).mpr
    by_contra hle
    have hlt : r < d := Nat.lt_of_not_ge hle
    have hc : x ∈ cosupport n univ (I.mul J) (r+d*2) :=
      inter_cosupport_subset_cosupport_mul r (d*2) ⟨hr,hx⟩
    have hc' := cosupport_anti (by omega : r*3+1 ≤ r+d*2) hc
    rw [hRed] at hc'
    obtain ⟨g,hg,hNot⟩ : ∃ g, I.mem x g ∧ ¬ (idealPow (pointIdeal n x) (r+1)).mem x g := by
      by_contra! hAll
      exact hnr ⟨mem_univ x,fun g hg => vanishesToOrderOn_of_mem (hAll g hg)⟩
    have hG := hHolI x g hg
    have hPow := mem_idealPow_of_vanishesToOrderOn_univ
      (hc'.2 _ (MonomialPart.pow_mem_idealPow hg hG 3))
    exact pow_notMem_idealPow hG hNot 3 (by simpa [Nat.mul_comm] using hPow)

private theorem factor_mul_factor {n : ℕ} {X : CMfd.{0} n}
    (L A B : GermIdeal n X) (hL : L.IsCoherent) (hA : A.IsCoherent) (hB : B.IsCoherent)
    (a b : ℕ) :
    ((idealPow L a).mul A).mul ((idealPow L b).mul B) =
      (idealPow L (a+b)).mul (A.mul B) := by
  let A₀ := idealPow L a
  let B₀ := idealPow L b
  have ha : A₀.IsCoherent := GermIdealPullbackCalculus.isCoherent_idealPow hL a
  have hb : B₀.IsCoherent := GermIdealPullbackCalculus.isCoherent_idealPow hL b
  have hc := IdealWeightPowers.isCoherent_mul hb hB
  change (A₀.mul A).mul (B₀.mul B) = _
  rw [GermIdealTotalTransform.mul_assoc ha hA hc,
    ← GermIdealTotalTransform.mul_assoc hA hb hB, RestrictLeCalculus.mul_comm' A B₀,
    GermIdealTotalTransform.mul_assoc hb hA hB,
    ← GermIdealTotalTransform.mul_assoc ha hb (IdealWeightPowers.isCoherent_mul hA hB)]
  rw [RestrictLeCalculus.idealPow_add hL]

/-- The cubic reduction identity persists along a single common controlled
step at marks d and 2d. The full exceptional factor is cancelled exactly. -/
theorem square_reduction_geoTransform {n : ℕ} {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : P.ideal.IsCoherent) (hQ : Q.ideal.IsCoherent)
    (hPN : P.N = univ) (hQN : Q.N = univ) (hd : Q.d = P.d*2)
    (hRed : P.ideal.mul Q.ideal = idealPow P.ideal 3)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hpC : P.IsAdmissibleCentre C) (hqC : Q.IsAdmissibleCentre C) :
    (P.geoTransform C π).ideal.mul (Q.geoTransform C π).ideal =
      idealPow (P.geoTransform C π).ideal 3 := by
  let T : BlowupTower X Y := .step .refl C π hπ
  let A := (P.geoTransform C π).ideal
  let B := (Q.geoTransform C π).ideal
  let L := (BlowupTowerTransforms.exceptionalDivisor T).ideal
  obtain ⟨_, ha, hp⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := P) hPN hP T ⟨trivial,hpC⟩
  obtain ⟨_, hb, hq⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := Q) hQN hQ T ⟨trivial,hqC⟩
  change A.IsCoherent at ha
  change B.IsCoherent at hb
  change GermIdeal.pullback (m := n) T.proj P.ideal = (idealPow L P.d).mul A at hp
  change GermIdeal.pullback (m := n) T.proj Q.ideal = (idealPow L Q.d).mul B at hq
  have hLi : L.IsInvertible := (BlowupTowerTransforms.exceptionalDivisor T).isInvertible
  have hLc := DivisorMetric.isCoherent_of_isInvertible hLi
  have hPull := congrArg (GermIdeal.pullback (m := n) T.proj) hRed
  rw [GermIdealTotalTransform.pullback_mul T.contMDiff_proj hP hQ,
    BlowupExceptionalDivisor.pullback_idealPow T.contMDiff_proj hP, hp,hq] at hPull
  rw [factor_mul_factor L A B hLc ha hb, hd,
    BlowupControlledTransform.idealPow_mul (GermIdealPullbackCalculus.isCoherent_idealPow hLc _) ha,
    MarkedIdealOperationsTransform.idealPow_idealPow hLc, show P.d + P.d*2 = P.d*3 by omega] at hPull
  have hEq := congrArg (fun I => InvertibleIdealQuotient.colon I (idealPow L (P.d*3))) hPull
  have hi := BlowupExceptionalDivisor.isInvertible_idealPow hLi (P.d*3)
  rw [BlowupControlledTransform.colon_mul_eq hi (IdealWeightPowers.isCoherent_mul ha hb),
    BlowupControlledTransform.colon_mul_eq hi (GermIdealPullbackCalculus.isCoherent_idealPow ha 3)] at hEq
  exact hEq

/-- The stable relation underlying actual mixed test equivalence under
a cubic reduction. It remembers the exact ordered boundary. -/
def SquareReduction {n : ℕ} {X : CMfd.{0} n} (P Q : MarkedIdeal n X) : Prop :=
  ∃ k l : ℕ, IsInvDomain k P ∧ IsInvDomain l Q ∧ P.N = univ ∧ Q.N = univ ∧
    P.E = Q.E ∧ Q.d = P.d * 2 ∧ P.ideal.mul Q.ideal = idealPow P.ideal 3

private theorem square_reduction_pullback {n m : ℕ} {X : CMfd.{0} n} {Y : CMfd.{0} m}
    (P Q : MarkedIdeal n X) (hp : P.ideal.IsCoherent) (hq : Q.ideal.IsCoherent)
    (hRed : P.ideal.mul Q.ideal = idealPow P.ideal 3) {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    (GermIdeal.pullback (m := m) f P.ideal).mul (GermIdeal.pullback (m := m) f Q.ideal) =
      idealPow (GermIdeal.pullback (m := m) f P.ideal) 3 := by
  rw [← HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hf hp hq, hRed,
    HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hf hp]

private theorem square_reduction_isLocStable : IsLocStable Kinds.wp (@SquareReduction) where
  E_eq := by
    rintro n X P Q ⟨_,_,_,_,_,_,hE,_,_⟩
    exact hE.symm
  cosupp_eq := by
    rintro n X P Q ⟨_,_,hp,hq,hPN,hQN,_,hd,hRed⟩
    unfold MarkedIdeal.cosupp
    rw [hPN,hQN,hd]
    exact square_reduction_cosupport P.ideal Q.ideal hp.isWellFormed.isCoherent
      hq.isWellFormed.isCoherent (hPN ▸ hp.isNonzeroAlongAt) hRed P.d
  controlled := by
    rintro n X P Q ⟨k,l,hp,hq,hPN,hQN,hE,hd,hRed⟩ C Y π hπ hPC
    have hCos : P.cosupp = Q.cosupp := by
      unfold MarkedIdeal.cosupp
      rw [hPN,hQN,hd]
      exact square_reduction_cosupport P.ideal Q.ideal hp.isWellFormed.isCoherent
        hq.isWellFormed.isCoherent (hPN ▸ hp.isNonzeroAlongAt) hRed P.d
    have hQC := (isAdmissibleCentre_congr hE hCos C).mp hPC
    have hpT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hp (.step .refl C π hπ) ⟨trivial,hPC⟩
    have hqT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hq (.step .refl C π hπ) ⟨trivial,hQC⟩
    exact ⟨k,l,hpT,hqT,geoTransform_N_eq_univ hPN hπ,geoTransform_N_eq_univ hQN hπ,
      congrArg (fun E : List (Set X) => E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) hE,
      hd,square_reduction_geoTransform P Q hp.isWellFormed.isCoherent hq.isWellFormed.isCoherent
        hPN hQN hd hRed hπ hPC hQC⟩
  projection := by
    rintro _ n X P Q ⟨k,l,hp,hq,hPN,hQN,hE,hd,hRed⟩
    refine ⟨k+1,l+1,projection_test_isInvDomain P hp,projection_test_isInvDomain Q hq,
      by simp [projectionTest,hPN],by simp [projectionTest,hQN],?_,hd,?_⟩
    · unfold projectionTest
      rw [hE]
    · exact square_reduction_pullback P Q hp.isWellFormed.isCoherent hq.isWellFormed.isCoherent
        hRed (ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1))
  restrict := by
    rintro n X P Q ⟨k,l,hp,hq,hPN,hQN,hE,hd,hRed⟩ U
    refine ⟨k,l,InvDomainTowerAlong.isInvDomain_pullback_val U hp,
       InvDomainTowerAlong.isInvDomain_pullback_val U hq,?_,?_,?_,hd,?_⟩
    · change (Subtype.val : U → X) ⁻¹' P.N = univ
      rw [hPN,preimage_univ]
    · change (Subtype.val : U → X) ⁻¹' Q.N = univ
      rw [hQN,preimage_univ]
    · exact congrArg (fun E => E.map ((Subtype.val : U → X) ⁻¹' ·)) hE
    · exact square_reduction_pullback P Q hp.isWellFormed.isCoherent hq.isWellFormed.isCoherent
        hRed contMDiff_subtype_val

/-- The actual cubic identity is sufficient for all local admissible
blowups, line tests, and open restrictions, with no raw ideal equality. -/
theorem locWPEquiv_of_square_reduction {n : ℕ} {X : CMfd.{0} n}
    {P Q : MarkedIdeal n X} (h : SquareReduction P Q) : LocWPEquiv P Q :=
  LocEquiv.of_isLocStable square_reduction_isLocStable rfl h

private theorem sumIdeal_le_coherent {n : ℕ} {X : CMfd.{0} n}
    {A B C : GermIdeal n X} (hC : C.IsCoherent) (ha : A.Le C) (hb : B.Le C) :
    (sumIdeal A B).Le C := by
  intro x g hg
  obtain ⟨U,hU,hxU,N,s,hs,hgen⟩ := hC x
  apply (hgen x hxU g).mpr
  exact IsInSpanAt.trans (fun f hf => (hgen x hxU f).mp (hf.elim (ha x f) (hb x f)))
    (mem_sumIdeal_iff.mp hg)

private theorem germ_ideal_eq_of_le {n : ℕ} {X : CMfd.{0} n}
    {A B : GermIdeal n X} (ha : A.Le B) (hb : B.Le A) : A = B := by
  ext x g
  exact ⟨ha x g,hb x g⟩

set_option maxHeartbeats 1400000 in
/-- Two coherent generators, or two coherent summands, give the exact
cubic reduction for their separate squares. -/
theorem binary_square_cubic_reduction {n : ℕ} {X : CMfd.{0} n}
    (A B : GermIdeal n X) (ha : A.IsCoherent) (hb : B.IsCoherent) :
    let I := sumIdeal A B
    let J := sumIdeal (idealPow A 2) (idealPow B 2)
    I.mul J = idealPow I 3 := by
  let I := sumIdeal A B
  let J := sumIdeal (idealPow A 2) (idealPow B 2)
  have hi := isCoherent_sumIdeal ha hb
  have ha₂ := GermIdealPullbackCalculus.isCoherent_idealPow ha 2
  have hb₂ := GermIdealPullbackCalculus.isCoherent_idealPow hb 2
  have hj := isCoherent_sumIdeal ha₂ hb₂
  have hHol {D : GermIdeal n X} (hc : D.IsCoherent) : ∀ x g, D.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg
  have haI : A.Le I := le_sumIdeal_left' (hHol ha)
  have hbI : B.Le I := le_sumIdeal_right' (hHol hb)
  have haJ : (idealPow A 2).Le J := le_sumIdeal_left' (hHol ha₂)
  have hbJ : (idealPow B 2).Le J := le_sumIdeal_right' (hHol hb₂)
  have hId {D : GermIdeal n X} : D.Le D := fun _ _ h => h
  have hTwo (D : GermIdeal n X) (h : D.IsCoherent) : idealPow D 2 = D.mul D := by
    rw [show (2:ℕ) = 1+1 by decide, idealPow_succ, show (1:ℕ) = 0+1 by decide,
      idealPow_succ, idealPow_zero, BlowupControlledTransform.unitIdeal_mul h]
  have hThree : idealPow I 3 = (I.mul I).mul I := by
    rw [show (3:ℕ) = 2+1 by decide, idealPow_succ, hTwo I hi]
  intro I' J'
  change I.mul J = idealPow I 3
  rw [hThree]
  apply germ_ideal_eq_of_le
  · rw [RestrictLeCalculus.mul_comm' (I.mul I) I, ← hTwo I hi]
    exact MarkedIdealOperationsTransform.mul_le_mul' hId
      (sumIdeal_le_coherent (GermIdealPullbackCalculus.isCoherent_idealPow hi 2)
        (MarkedIdealOperationsTransform.idealPow_mono haI 2)
        (MarkedIdealOperationsTransform.idealPow_mono hbI 2))
  · have hGoal := IdealWeightPowers.isCoherent_mul hi hj
    have hAA : (A.mul A).Le J := by rw [← hTwo A ha]; exact haJ
    have hBB : (B.mul B).Le J := by rw [← hTwo B hb]; exact hbJ
    have hAAB : ((A.mul B).mul A).Le (I.mul J) := by
      rw [RestrictLeCalculus.mul_comm' A B, GermIdealTotalTransform.mul_assoc hb ha ha]
      exact MarkedIdealOperationsTransform.mul_le_mul' hbI hAA
    have hABB : ((A.mul B).mul B).Le (I.mul J) := by
      rw [GermIdealTotalTransform.mul_assoc ha hb hb]
      exact MarkedIdealOperationsTransform.mul_le_mul' haI hBB
    have hMixed : (I.mul (A.mul B)).Le (I.mul J) := by
      rw [RestrictLeCalculus.mul_comm' I (A.mul B)]
      change ((A.mul B).mul (sumIdeal A B)).Le (I.mul J)
      rw [MarkedIdealOperationsTransform.mul_sumIdeal (hHol (IdealWeightPowers.isCoherent_mul ha hb))
        (hHol ha) (hHol hb)]
      exact sumIdeal_le_coherent hGoal hAAB hABB
    have hLeft : ((I.mul I).mul A).Le (I.mul J) := by
      rw [GermIdealTotalTransform.mul_assoc hi hi ha, RestrictLeCalculus.mul_comm' I A]
      change (I.mul (A.mul (sumIdeal A B))).Le (I.mul J)
      rw [MarkedIdealOperationsTransform.mul_sumIdeal (hHol ha) (hHol ha) (hHol hb),
        MarkedIdealOperationsTransform.mul_sumIdeal (hHol hi)
          (hHol (IdealWeightPowers.isCoherent_mul ha ha)) (hHol (IdealWeightPowers.isCoherent_mul ha hb))]
      exact sumIdeal_le_coherent hGoal (MarkedIdealOperationsTransform.mul_le_mul' hId hAA) hMixed
    have hRight : ((I.mul I).mul B).Le (I.mul J) := by
      rw [GermIdealTotalTransform.mul_assoc hi hi hb, RestrictLeCalculus.mul_comm' I B]
      change (I.mul (B.mul (sumIdeal A B))).Le (I.mul J)
      rw [MarkedIdealOperationsTransform.mul_sumIdeal (hHol hb) (hHol ha) (hHol hb),
        MarkedIdealOperationsTransform.mul_sumIdeal (hHol hi)
          (hHol (IdealWeightPowers.isCoherent_mul hb ha)) (hHol (IdealWeightPowers.isCoherent_mul hb hb)),
        RestrictLeCalculus.mul_comm' B A]
      exact sumIdeal_le_coherent hGoal hMixed (MarkedIdealOperationsTransform.mul_le_mul' hId hBB)
    change ((I.mul I).mul (sumIdeal A B)).Le (I.mul J)
    rw [MarkedIdealOperationsTransform.mul_sumIdeal (hHol (IdealWeightPowers.isCoherent_mul hi hi))
      (hHol ha) (hHol hb)]
    exact sumIdeal_le_coherent hGoal hLeft hRight

/-- Explicit native-style two-generator square compression has all local
weak projection tests of the unpowered mark-d reference. -/
theorem binary_square_locWPEquiv {n : ℕ} {X : CMfd.{0} n}
    (A B : GermIdeal n X) (ha : A.IsCoherent) (hb : B.IsCoherent) (E : List (Set X)) (d : ℕ)
    (hp : IsInvDomain n (⟨univ,E,sumIdeal A B,d⟩ : MarkedIdeal n X))
    (hq : IsInvDomain n (⟨univ,E,sumIdeal (idealPow A 2) (idealPow B 2),d*2⟩ : MarkedIdeal n X)) :
    LocWPEquiv (⟨univ,E,sumIdeal A B,d⟩ : MarkedIdeal n X)
      (⟨univ,E,sumIdeal (idealPow A 2) (idealPow B 2),d*2⟩ : MarkedIdeal n X) := by
  exact locWPEquiv_of_square_reduction ⟨n,n,hp,hq,rfl,rfl,rfl,rfl,binary_square_cubic_reduction A B ha hb⟩

open HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression

private theorem two_function_ideal_eq_sum {n : ℕ} {X : CMfd.{0} n}
    (f g : X → ℂ) (hf : ∀ x, HolomorphicAt n f x) (hg : ∀ x, HolomorphicAt n g x) :
    finiteFunctionIdeal (n := n) (Sum.elim (fun _ : Unit => f) (fun _ : Unit => g)) =
      sumIdeal (finiteFunctionIdeal (fun _ : Unit => f)) (finiteFunctionIdeal (fun _ : Unit => g)) := by
  ext x a
  constructor
  · intro ha
    change IsInSpanAt (n := n) (fun s => (finiteFunctionIdeal (fun _ : Unit => f)).mem x s ∨
      (finiteFunctionIdeal (fun _ : Unit => g)).mem x s) x a
    apply IsInSpanAt.mono _ ha
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl i => exact Or.inl (isInSpanAt_self ⟨i,rfl⟩ (hf x))
    | inr i => exact Or.inr (isInSpanAt_self ⟨i,rfl⟩ (hg x))
  · intro ha
    change IsInSpanAt (n := n) (fun s => (finiteFunctionIdeal (fun _ : Unit => f)).mem x s ∨
      (finiteFunctionIdeal (fun _ : Unit => g)).mem x s) x a at ha
    refine IsInSpanAt.trans (fun b hb => ?_) ha
    rcases hb with hb | hb
    · exact IsInSpanAt.mono (fun c ⟨i,hi⟩ => ⟨Sum.inl i,hi⟩) hb
    · exact IsInSpanAt.mono (fun c ⟨i,hi⟩ => ⟨Sum.inr i,hi⟩) hb

private theorem singleton_function_ideal_square {n : ℕ} {X : CMfd.{0} n}
    (f : X → ℂ) (hf : ∀ x, HolomorphicAt n f x) :
    idealPow (finiteFunctionIdeal (n := n) (fun _ : Unit => f)) 2 =
      finiteFunctionIdeal (fun _ : Unit => f^2) := by
  ext x a
  have hSingle (g : X → ℂ) (b : X → ℂ) :
      (finiteFunctionIdeal (n := n) (fun _ : Unit => g)).mem x b ↔
        IsInSpanAt (n := n) (· = g) x b := by
    change IsInSpanAt (n := n) (fun c => c ∈ range (fun _ : Unit => g)) x b ↔ _
    exact ⟨IsInSpanAt.mono (fun _ ⟨_,hc⟩ => hc.symm),
      IsInSpanAt.mono (fun _ hc => ⟨(),hc.symm⟩)⟩
  rw [hSingle]
  exact HironakaSharpActualProductNewExceptionalFactor.idealPow_principal_mem_iff (hf x)
    (hSingle f) 2 a

/-- Two genuine degree-two coefficient functions give a genuine raw
native mark-four record in the same weak-projection class as their
unpowered mark-two reference. No principality of the sum is used. -/
theorem two_quadratic_native_functions_locWPEquiv
    {n : ℕ} {X : CMfd.{0} n} (E : List (Set X))
    (f g : X → ℂ)
    (hf : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g) :
    let c := Sum.elim (fun _ : Unit => f) (fun _ : Unit => g)
    let P : MarkedIdeal n X := ⟨univ,E,finiteFunctionIdeal c,2⟩
    let Q : MarkedIdeal n X := ⟨univ,E,weightedFunctionIdeal (fun _ : Unit ⊕ Unit => 2) c,4⟩
    IsInvDomain n P → IsInvDomain n Q → LocWPEquiv P Q := by
  intro c P Q hp hq
  have hf' (x : X) : HolomorphicAt n f x := Filter.Eventually.of_forall fun y => hf y
  have hg' (x : X) : HolomorphicAt n g x := Filter.Eventually.of_forall fun y => hg y
  let A := finiteFunctionIdeal (n := n) (fun _ : Unit => f)
  let B := finiteFunctionIdeal (n := n) (fun _ : Unit => g)
  have ha : A.IsCoherent := isCoherent_finiteFunctionIdeal _ (fun _ => hf)
  have hb : B.IsCoherent := isCoherent_finiteFunctionIdeal _ (fun _ => hg)
  have hP : P = ⟨univ,E,sumIdeal A B,2⟩ :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl (two_function_ideal_eq_sum f g hf' hg') rfl
  have hQI : weightedFunctionIdeal (n := n) (fun _ : Unit ⊕ Unit => 2) c =
      sumIdeal (idealPow A 2) (idealPow B 2) := by
    unfold weightedFunctionIdeal
    have hMark : weightedCommonMark (fun _ : Unit ⊕ Unit => 2) = 4 := by
      simp [weightedCommonMark]
    rw [hMark]
    have hc : (fun (i : Unit ⊕ Unit) y => c i y ^ (4 / 2 : ℕ)) =
        Sum.elim (fun _ : Unit => f^2) (fun _ : Unit => g^2) := by
      funext i y
      cases i <;> rfl
    rw [hc, two_function_ideal_eq_sum (f^2) (g^2)
      (fun x => holomorphicAt_pow_of (hf' x) 2) (fun x => holomorphicAt_pow_of (hg' x) 2),
      singleton_function_ideal_square f hf', singleton_function_ideal_square g hg']
  have hQ : Q = ⟨univ,E,sumIdeal (idealPow A 2) (idealPow B 2),4⟩ :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hQI rfl
  rw [hP] at hp ⊢
  rw [hQ] at hq ⊢
  exact binary_square_locWPEquiv A B ha hb E 2 hp hq

/-- On a chosen native chart with two actual degree-two family members,
the literal function presentation supplies the originally missing class
premise. At empty initial boundary the exponent condition is automatic. -/
theorem native_two_quadratic_chart_low_canonical
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I : Type}
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : HironakaG8NativeRelativeClearing.NativeWindows X I W E H D)
    (T : BlowupTower X Y)
    (hSync : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages
      (CanonicalCentres.canonicalInvariant (n+1)) A.openSet A.powered T)
    (i : I) (P : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)))
    (hp : IsInvDomain (n+1) P) (hPN : P.N = univ) (hPE : P.E = []) (hd : P.d ≤ 2)
    (f g : A.openSet i → ℂ)
    (hf : MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) g) :
    let c := Sum.elim (fun _ : Unit => f) (fun _ : Unit => g)
    let R : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)) := ⟨univ,[],finiteFunctionIdeal c,2⟩
    IsInvDomain (n+1) R →
    A.record i = ⟨univ,[],weightedFunctionIdeal (fun _ : Unit ⊕ Unit => 2) c,4⟩ →
    NonmonomialOrderLocal.nmPart P = R.ideal →
    IsCanonical P ((CanonicalCentres.canonicalInvariant (n+1)).inv P)
      (BlowupTowerTransforms.restrict (A.openSet i) T) := by
  intro c R hr hRaw hResid
  have hQN : (A.record i).N = univ := congrArg MarkedIdeal.N hRaw
  have hQE : (A.record i).E = [] := congrArg MarkedIdeal.E hRaw
  have hQd : (A.record i).d = 4 := congrArg MarkedIdeal.d hRaw
  have hQDom := A.domain i
  rw [hRaw] at hQDom
  have hCl : LocWPEquiv R (A.record i) := by
    rw [hRaw]
    exact two_quadratic_native_functions_locWPEquiv (X := CMfd.of (n := n+1) (A.openSet i))
      [] f g hf hg hr hQDom
  have hActive (x : A.openSet i) (hx : x ∈ (A.record i).cosupp) :
      ordinaryTraceOrder (A.record i).N (A.record i).ideal x = (A.record i).d := by
    obtain ⟨_, _, hN, hI, V, S, k, a, w, hw, _, _, hMark, _, _, hAt⟩ := A.native i
    have hv : V.Nonempty := by
      by_contra hNo
      have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hNo
      have hOne : (A.record i).d = 1 := by
        rw [hMark]
        subst V
        simp [weightedCommonMark]
      omega
    have hOrd := (HironakaActualHistoricalNativeOrdinaryOrder.actual_native_point_ordinary_order
      S hv a w hw _ _ hN hI hMark x hx (hAt x hx)).1
    rwa [hN,hMark]
  exact HironakaG8EqualWeightNativeThresholds.native_simultaneous_canonical_via_residual_reference
    A.openSet A.record A.domain A.exponent A.positive T hSync i P R hp hr hPN rfl hQN
    hPE hd hResid hCl.symm (by simp [hQE]) hActive

end
end Hironaka.HironakaG8SquareReductionLocalEquiv
