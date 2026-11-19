import Hironaka.Resolution.HironakaG8EqualWeightNativeThresholds
import Hironaka.Resolution.HironakaG8LocalPower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8FinitePowerReductionLocalEquiv
noncomputable section

open scoped ProductComplexManifold

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings ProductComplexManifold HomogenizedGlueingTower GermIdealOrder IdealWeightPowers
  RelativePrincipalizationSpan OrderMultiplicativity GermOrderProduct OrderTaylor CompanionReduction IdealOrderArithmetic
  HironakaSharpOriginalProductTraceOrder ResolutionInvariantSpec HironakaG8LocalHistory
  HironakaG8LocalStable HironakaActualProjectionTestRecord HironakaG8MixedEquiv
  InvertibleIdealQuotient RestrictedIdealExtension ResolutionDriver ResolutionDriver

/-- The exact reduction identity implies all proportional ordinary cosupport thresholds. -/
theorem finite_power_reduction_cosupport {n : ℕ} {X : CMfd.{0} n}
    (I J : GermIdeal n X) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (hn : ∀ x ∈ (univ : Set X), DivisorExponentAlong.IsNonzeroAlongAt univ I x)
    (r e : ℕ) (he : 0 < e) (hRed : (idealPow I r).mul J = idealPow I (r+e)) (d : ℕ) :
    cosupport n univ I d = cosupport n univ J (d*e) := by
  ext x
  let o := ordinaryTraceOrder (X := X) univ I x
  have hOrder := ordinaryTraceOrder_cosupport_iff (X := X) isClosedSubmanifold_univ hI hn (mem_univ x)
  have ho : x ∈ cosupport n univ I o := (hOrder o).mpr le_rfl
  have hno : x ∉ cosupport n univ I (o+1) := fun h => Nat.not_succ_le_self o ((hOrder (o+1)).mp h)
  have hHolI := fun x g h => GermIdeal.IsCoherent.holomorphicAt_mem hI (x := x) (g := g) h
  have hHolJ := fun x g h => GermIdeal.IsCoherent.holomorphicAt_mem hJ (x := x) (g := g) h
  have hHolPow := fun x g h => GermIdeal.IsCoherent.holomorphicAt_mem
    (GermIdealPullbackCalculus.isCoherent_idealPow hI r) (x := x) (g := g) h
  obtain ⟨g,hg,hNot⟩ : ∃ g, I.mem x g ∧ ¬ (idealPow (pointIdeal n x) (o+1)).mem x g := by
    by_contra! hAll
    exact hno ⟨mem_univ x,fun g hg => vanishesToOrderOn_of_mem (hAll g hg)⟩
  have hG := hHolI x g hg
  have hPowBound (j : ℕ) : x ∉ cosupport n univ (idealPow I j) (o*j+1) := by
    intro hx
    have hPow := mem_idealPow_of_vanishesToOrderOn_univ
      (hx.2 _ (MonomialPart.pow_mem_idealPow hg hG j))
    exact pow_notMem_idealPow hG hNot j (by simpa [Nat.mul_comm] using hPow)
  constructor
  · intro hx
    have hle := (hOrder d).mp hx
    have hc : x ∈ cosupport n univ ((idealPow I r).mul J) (o*(r+e)) := by
      rw [hRed, cosupport_idealPow_mul_eq hHolI (by omega : 1 ≤ r+e)]
      exact ho
    have hOut := mem_cosupport_of_mem_cosupport_mul hHolPow hHolJ
      (Nat.mul_le_mul_left o (Nat.le_add_right r e)) hc (hPowBound r)
    rw [Nat.mul_add, Nat.add_sub_cancel_left] at hOut
    exact cosupport_anti (Nat.mul_le_mul_right e hle) hOut
  · intro hx
    apply (hOrder d).mpr
    by_contra hle
    have hlt : o < d := Nat.lt_of_not_ge hle
    have hc : x ∈ cosupport n univ ((idealPow I r).mul J) (o*r+d*e) :=
      inter_cosupport_subset_cosupport_mul (o*r) (d*e)
        ⟨cosupport_subset_cosupport_idealPow o r ho,hx⟩
    have hlt' := Nat.mul_lt_mul_of_pos_right hlt he
    have hle' : o*(r+e)+1 ≤ o*r+d*e := by rw [Nat.mul_add]; omega
    have hc' := cosupport_anti hle' hc
    rw [hRed] at hc'
    exact hPowBound (r+e) hc'

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

/-- The finite-power reduction identity persists along a single common controlled
step at marks d and de. The full exceptional factor is cancelled exactly. -/
theorem finite_power_reduction_geoTransform {n : ℕ} {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : P.ideal.IsCoherent) (hQ : Q.ideal.IsCoherent)
    (hPN : P.N = univ) (hQN : Q.N = univ) (r e : ℕ) (hd : Q.d = P.d*e) (hRed : (idealPow P.ideal r).mul Q.ideal = idealPow P.ideal (r+e))
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hpC : P.IsAdmissibleCentre C) (hqC : Q.IsAdmissibleCentre C) :
    (idealPow (P.geoTransform C π).ideal r).mul (Q.geoTransform C π).ideal =
      idealPow (P.geoTransform C π).ideal (r+e) := by
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
  have har := GermIdealPullbackCalculus.isCoherent_idealPow ha r
  have hPull := congrArg (GermIdeal.pullback (m := n) T.proj) hRed
  rw [GermIdealTotalTransform.pullback_mul T.contMDiff_proj
    (GermIdealPullbackCalculus.isCoherent_idealPow hP r) hQ,
    BlowupExceptionalDivisor.pullback_idealPow T.contMDiff_proj hP,
    BlowupExceptionalDivisor.pullback_idealPow T.contMDiff_proj hP, hp,hq] at hPull
  rw [BlowupControlledTransform.idealPow_mul (GermIdealPullbackCalculus.isCoherent_idealPow hLc _) ha,
    MarkedIdealOperationsTransform.idealPow_idealPow hLc,
    factor_mul_factor L (idealPow A r) B hLc har hb, hd,
    BlowupControlledTransform.idealPow_mul (GermIdealPullbackCalculus.isCoherent_idealPow hLc _) ha,
    MarkedIdealOperationsTransform.idealPow_idealPow hLc, ← Nat.mul_add] at hPull
  have hEq := congrArg (fun I => InvertibleIdealQuotient.colon I (idealPow L (P.d*(r+e)))) hPull
  have hi := BlowupExceptionalDivisor.isInvertible_idealPow hLi (P.d*(r+e))
  rw [BlowupControlledTransform.colon_mul_eq hi (IdealWeightPowers.isCoherent_mul har hb),
    BlowupControlledTransform.colon_mul_eq hi (GermIdealPullbackCalculus.isCoherent_idealPow ha (r+e))] at hEq
  exact hEq

/-- The stable relation underlying actual mixed test equivalence under
a finite-power reduction. It remembers the exact ordered boundary. -/
def FinitePowerReduction {n : ℕ} {X : CMfd.{0} n} (P Q : MarkedIdeal n X) : Prop :=
  ∃ k l r e : ℕ, 0 < e ∧ IsInvDomain k P ∧ IsInvDomain l Q ∧ P.N = univ ∧ Q.N = univ ∧
    P.E = Q.E ∧ Q.d = P.d * e ∧ (idealPow P.ideal r).mul Q.ideal = idealPow P.ideal (r+e)

private theorem finite_power_reduction_pullback {n m : ℕ} {X : CMfd.{0} n} {Y : CMfd.{0} m}
    (P Q : MarkedIdeal n X) (hp : P.ideal.IsCoherent) (hq : Q.ideal.IsCoherent)
    (r e : ℕ) (hRed : (idealPow P.ideal r).mul Q.ideal = idealPow P.ideal (r+e)) {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    (idealPow (GermIdeal.pullback (m := m) f P.ideal) r).mul (GermIdeal.pullback (m := m) f Q.ideal) =
      idealPow (GermIdeal.pullback (m := m) f P.ideal) (r+e) := by
  rw [← HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hf hp,
    ← HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hf
      (GermIdealPullbackCalculus.isCoherent_idealPow hp r) hq, hRed,
    HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hf hp]

private theorem finite_power_reduction_isLocStable : IsLocStable Kinds.wp (@FinitePowerReduction) where
  E_eq := by
    rintro n X P Q ⟨_,_,_,_,_,_,_,_,_,hE,_,_⟩
    exact hE.symm
  cosupp_eq := by
    rintro n X P Q ⟨_,_,r,e,he,hp,hq,hPN,hQN,_,hd,hRed⟩
    unfold MarkedIdeal.cosupp
    rw [hPN,hQN,hd]
    exact finite_power_reduction_cosupport P.ideal Q.ideal hp.isWellFormed.isCoherent
      hq.isWellFormed.isCoherent (hPN ▸ hp.isNonzeroAlongAt) r e he hRed P.d
  controlled := by
    rintro n X P Q ⟨k,l,r,e,he,hp,hq,hPN,hQN,hE,hd,hRed⟩ C Y π hπ hPC
    have hCos : P.cosupp = Q.cosupp := by
      unfold MarkedIdeal.cosupp
      rw [hPN,hQN,hd]
      exact finite_power_reduction_cosupport P.ideal Q.ideal hp.isWellFormed.isCoherent
        hq.isWellFormed.isCoherent (hPN ▸ hp.isNonzeroAlongAt) r e he hRed P.d
    have hQC := (isAdmissibleCentre_congr hE hCos C).mp hPC
    have hpT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hp (.step .refl C π hπ) ⟨trivial,hPC⟩
    have hqT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hq (.step .refl C π hπ) ⟨trivial,hQC⟩
    exact ⟨k,l,r,e,he,hpT,hqT,geoTransform_N_eq_univ hPN hπ,geoTransform_N_eq_univ hQN hπ,
      congrArg (fun E : List (Set X) => E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) hE,
      hd,finite_power_reduction_geoTransform P Q hp.isWellFormed.isCoherent hq.isWellFormed.isCoherent
        hPN hQN r e hd hRed hπ hPC hQC⟩
  projection := by
    rintro _ n X P Q ⟨k,l,r,e,he,hp,hq,hPN,hQN,hE,hd,hRed⟩
    refine ⟨k+1,l+1,r,e,he,projection_test_isInvDomain P hp,projection_test_isInvDomain Q hq,
      by simp [projectionTest,hPN],by simp [projectionTest,hQN],?_,hd,?_⟩
    · unfold projectionTest
      rw [hE]
    · exact finite_power_reduction_pullback P Q hp.isWellFormed.isCoherent hq.isWellFormed.isCoherent
        r e hRed (ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1))
  restrict := by
    rintro n X P Q ⟨k,l,r,e,he,hp,hq,hPN,hQN,hE,hd,hRed⟩ U
    refine ⟨k,l,r,e,he,InvDomainTowerAlong.isInvDomain_pullback_val U hp,
       InvDomainTowerAlong.isInvDomain_pullback_val U hq,?_,?_,?_,hd,?_⟩
    · change (Subtype.val : U → X) ⁻¹' P.N = univ
      rw [hPN,preimage_univ]
    · change (Subtype.val : U → X) ⁻¹' Q.N = univ
      rw [hQN,preimage_univ]
    · exact congrArg (fun E => E.map ((Subtype.val : U → X) ⁻¹' ·)) hE
    · exact finite_power_reduction_pullback P Q hp.isWellFormed.isCoherent hq.isWellFormed.isCoherent
        r e hRed contMDiff_subtype_val

/-- The actual finite-power identity is sufficient for all local admissible
blowups, line tests, and open restrictions, with no raw ideal equality. -/
theorem locWPEquiv_of_finite_power_reduction {n : ℕ} {X : CMfd.{0} n}
    {P Q : MarkedIdeal n X} (h : FinitePowerReduction P Q) : LocWPEquiv P Q :=
  LocEquiv.of_isLocStable finite_power_reduction_isLocStable rfl h

open HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression

private def familyMonomial {ι X : Type} [Fintype ι]
    (f : ι → X → ℂ) (a : ι → ℕ) : X → ℂ :=
  fun x => ∏ i, f i x ^ a i

private theorem familyMonomial_add {ι X : Type} [Fintype ι]
    (f : ι → X → ℂ) (a b : ι → ℕ) :
    familyMonomial f (a+b) = familyMonomial f a * familyMonomial f b := by
  funext x
  simp only [familyMonomial,Pi.add_apply,Pi.mul_apply,pow_add,Finset.prod_mul_distrib]

private def exponentAt {ι : Type} [DecidableEq ι] (i : ι) (e : ℕ) : ι → ℕ :=
  fun j => if j = i then e else 0

private theorem exponentAt_total {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (e : ℕ) : ∑ j, exponentAt i e j = e := by
  classical
  rw [Finset.sum_eq_single i]
  · simp [exponentAt]
  · intro j _ hj
    simp [exponentAt,hj]
  · simp

private theorem familyMonomial_single {ι X : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → X → ℂ) (i : ι) (e : ℕ) :
    familyMonomial f (exponentAt i e) = f i ^ e := by
  funext x
  unfold familyMonomial
  rw [Finset.prod_eq_single i]
  · simp [exponentAt]
  · intro j _ hj
    simp [exponentAt,hj]
  · simp

private theorem familyMonomial_split {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (i : ι) (e : ℕ) (he : e ≤ a i) :
    (a - exponentAt i e) + exponentAt i e = a := by
  funext j
  change a j - exponentAt i e j + exponentAt i e j = a j
  by_cases hj : j = i
  · subst j
    simpa [exponentAt] using Nat.sub_add_cancel he
  · simp [exponentAt,hj]

private theorem familyMonomial_total_split {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (i : ι) (e : ℕ) (he : e ≤ a i) :
    (∑ j, (a - exponentAt i e) j) + e = ∑ j, a j := by
  have h := congrArg (fun b : ι → ℕ => ∑ j, b j) (familyMonomial_split a i e he)
  change (∑ j, ((a - exponentAt i e) j + exponentAt i e j)) = _ at h
  rw [Finset.sum_add_distrib, exponentAt_total] at h
  exact h

private theorem holomorphicAt_familyMonomial {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι]
    (f : ι → X → ℂ) (x : X) (hf : ∀ i, HolomorphicAt n (f i) x) (a : ι → ℕ) :
    HolomorphicAt n (familyMonomial f a) x :=
  MonomialPart.holomorphicAt_finset_prod Finset.univ
    (fun i _ => holomorphicAt_pow_of (hf i) _)

private theorem mul_of_local_spans {n : ℕ} {X : CMfd.{0} n}
    {S T : (X → ℂ) → Prop} {x : X} {a b : X → ℂ}
    (ha : IsInSpanAt (n := n) S x a) (hb : IsInSpanAt (n := n) T x b) :
    IsInSpanAt (n := n) (fun t => ∃ s s', S s ∧ T s' ∧ t = s*s') x (a*b) := by
  have h := MarkedIdealOperationsAlong.IsInSpanOnAt.mul (W := univ) (RelativePrincipalizationSpan.IsInSpanAt.restrict ha) (RelativePrincipalizationSpan.IsInSpanAt.restrict hb)
  obtain ⟨N,s,c,hs,hc,hEq⟩ := h
  exact ⟨ha.1.mul hb.1,N,s,c,hs,hc,hEq.mono (fun _ h => h trivial)⟩

set_option maxHeartbeats 1400000 in
/-- The literal ambient power of a coherent generator ideal is generated
by the actual products of the requested degree. -/
private theorem finiteFunctionIdeal_pow_span {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι]
    (f : ι → X → ℂ) (x : X) (hf : ∀ i, HolomorphicAt n (f i) x) (k : ℕ) (g : X → ℂ) :
    (idealPow (finiteFunctionIdeal (n := n) f) k).mem x g ↔
      IsInSpanAt (n := n) (fun s => ∃ a : ι → ℕ, (∑ i, a i) = k ∧ s = familyMonomial f a) x g := by
  classical
  induction k generalizing g with
  | zero =>
    constructor
    · intro hg
      change HolomorphicAt n g x at hg
      have hOne : (1 : X → ℂ) = familyMonomial f (fun _ => 0) := by funext y; simp [familyMonomial]
      exact isInSpanAt_of_eq_mul (a := g) (s := 1) ⟨fun _ => 0,by simp,hOne⟩ hg hg
        (Filter.Eventually.of_forall fun _ => (mul_one _).symm)
    · exact fun hg => hg.1
  | succ k ih =>
    rw [idealPow_succ]
    constructor
    · intro hg
      refine IsInSpanAt.trans ?_ (InvertibleIdealQuotient.mem_mul_iff.mp hg)
      rintro _ ⟨u,v,hu,hv,rfl⟩
      have hu' := (ih u).mp hu
      have hv' : IsInSpanAt (n := n) (fun s => s ∈ range f) x v := hv
      refine IsInSpanAt.mono ?_ (mul_of_local_spans hu' hv')
      rintro _ ⟨s,_,⟨a,ha,rfl⟩,⟨i,rfl⟩,rfl⟩
      refine ⟨a + exponentAt i 1,?_ ,?_⟩
      · change (∑ j, (a j + exponentAt i 1 j)) = k+1
        rw [Finset.sum_add_distrib,ha,exponentAt_total]
      · rw [familyMonomial_add,familyMonomial_single,pow_one]
    · intro hg
      apply InvertibleIdealQuotient.mem_mul_iff.mpr
      refine IsInSpanAt.mono ?_ hg
      rintro _ ⟨a,ha,rfl⟩
      obtain ⟨i,hi⟩ : ∃ i, 1 ≤ a i := by
        by_contra! hz
        have hz' : ∀ i, a i = 0 := fun i => by have := hz i; omega
        simp [hz'] at ha
      let b := a - exponentAt i 1
      have hb : (∑ j, b j) = k := by
        have h := familyMonomial_total_split a i 1 hi
        rw [ha] at h
        exact Nat.add_right_cancel h
      have hU : (idealPow (finiteFunctionIdeal (n := n) f) k).mem x (familyMonomial f b) :=
        (ih _).mpr (isInSpanAt_self ⟨b,hb,rfl⟩ (holomorphicAt_familyMonomial f x hf b))
      have hV : (finiteFunctionIdeal (n := n) f).mem x (f i) := isInSpanAt_self ⟨i,rfl⟩ (hf i)
      refine ⟨familyMonomial f b, f i,hU,hV,?_⟩
      have h := congrArg (familyMonomial f) (familyMonomial_split a i 1 hi)
      rw [familyMonomial_add,familyMonomial_single,pow_one] at h
      exact h.symm

set_option maxHeartbeats 1400000 in
/-- Every genuine degree-(r+e) product contains an e-th power of a
generator once its degree exceeds the pigeonhole bound. The conclusion
is an equality of the whole ambient coherent ideals. -/
theorem finite_function_power_reduction
    {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι]
    (f : ι → X → ℂ) (hf : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (f i))
    (r e : ℕ) (he : 0 < e) (hBound : Fintype.card ι * (e-1) < r+e) :
    let I := finiteFunctionIdeal (n := n) f
    let J := finiteFunctionIdeal (n := n) (fun i => f i ^ e)
    (idealPow I r).mul J = idealPow I (r+e) := by
  classical
  intro I J
  have hI : I.IsCoherent := isCoherent_finiteFunctionIdeal f hf
  have hF (x : X) (i : ι) : HolomorphicAt n (f i) x :=
    Filter.Eventually.of_forall fun y => hf i y
  have hJI : J.Le (idealPow I e) := by
    intro x g hg
    apply (finiteFunctionIdeal_pow_span f x (hF x) e g).mpr
    refine IsInSpanAt.mono ?_ hg
    rintro _ ⟨i,rfl⟩
    exact ⟨exponentAt i e,exponentAt_total i e,(familyMonomial_single f i e).symm⟩
  ext x g
  constructor
  · intro hg
    rw [RestrictLeCalculus.idealPow_add hI]
    exact MarkedIdealOperationsTransform.mul_le_mul' (fun _ _ h => h) hJI x g hg
  · intro hg
    apply InvertibleIdealQuotient.mem_mul_iff.mpr
    refine IsInSpanAt.mono ?_ ((finiteFunctionIdeal_pow_span f x (hF x) (r+e) g).mp hg)
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨i,hi⟩ : ∃ i, e ≤ a i := by
      by_contra! hn
      have hLe : (∑ j, a j) ≤ ∑ _j : ι, (e-1) :=
        Finset.sum_le_sum fun j _ => by have := hn j; omega
      rw [ha,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hLe
      exact (not_le.mpr hBound) hLe
    let b := a - exponentAt i e
    have hb : (∑ j, b j) = r := by
      have h := familyMonomial_total_split a i e hi
      rw [ha] at h
      exact Nat.add_right_cancel h
    have hB : (idealPow I r).mem x (familyMonomial f b) :=
      (finiteFunctionIdeal_pow_span f x (hF x) r _).mpr
        (isInSpanAt_self ⟨b,hb,rfl⟩ (holomorphicAt_familyMonomial f x (hF x) b))
    have hJ : J.mem x (f i ^ e) := isInSpanAt_self ⟨i,rfl⟩ (holomorphicAt_pow_of (hF x i) e)
    refine ⟨familyMonomial f b,f i^e,hB,hJ,?_⟩
    have h := congrArg (familyMonomial f) (familyMonomial_split a i e hi)
    rw [familyMonomial_add,familyMonomial_single] at h
    exact h.symm

/-- Actual uniform powered generators and the unpowered true-mark
reference have identical local admissible, projection and restriction tests. -/
theorem finite_function_power_locWPEquiv
    {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι]
    (f : ι → X → ℂ) (hf : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (f i))
    (d e : ℕ) (he : 0 < e) (E : List (Set X)) :
    let P : MarkedIdeal n X := ⟨univ,E,finiteFunctionIdeal f,d⟩
    let Q : MarkedIdeal n X := ⟨univ,E,finiteFunctionIdeal (fun i => f i ^ e),d*e⟩
    IsInvDomain n P → IsInvDomain n Q → LocWPEquiv P Q := by
  intro P Q hp hq
  let r := Fintype.card ι * (e-1)
  have hRed := finite_function_power_reduction f hf r e he (by dsimp [r]; omega)
  exact locWPEquiv_of_finite_power_reduction
    ⟨n,n,r,e,he,hp,hq,rfl,rfl,rfl,rfl,hRed⟩

/-- A finite equal native weight family uses a single compression exponent
and therefore lies in the same local class as its unpowered true-mark span. -/
theorem equal_weight_native_functions_locWPEquiv
    {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι] [Nonempty ι]
    (f : ι → X → ℂ) (hf : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (f i))
    (d : ℕ) (hd : 0 < d) (E : List (Set X)) :
    let w : ι → ℕ := fun _ => d
    let P : MarkedIdeal n X := ⟨univ,E,finiteFunctionIdeal f,d⟩
    let Q : MarkedIdeal n X := ⟨univ,E,weightedFunctionIdeal w f,weightedCommonMark w⟩
    IsInvDomain n P → IsInvDomain n Q → LocWPEquiv P Q := by
  intro w P Q hp hq
  let e := weightedCommonMark w / d
  let i : ι := Classical.choice inferInstance
  have he : 0 < e := compressionExponent_pos w (fun _ => hd) i
  have hm : d * e = weightedCommonMark w := weight_mul_compressionExponent w i
  have hQ : Q = ⟨univ,E,finiteFunctionIdeal (fun i => f i ^ e),d*e⟩ :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl rfl hm.symm
  rw [hQ] at hq ⊢
  exact finite_function_power_locWPEquiv f hf d e he E hp hq

/-- The actual weighted stage certificate supplies low canonicality
on a chart whose finite equal-weight source functions generate the
unpowered residual reference. Initial empty boundary makes the
normalized exponent premise immediate. -/
theorem native_equal_weight_chart_low_canonical
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I ι : Type} [Fintype ι] [Nonempty ι]
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : HironakaG8NativeRelativeClearing.NativeWindows X I W E H D)
    (T : BlowupTower X Y)
    (hSync : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages
      (CanonicalCentres.canonicalInvariant (n+1)) A.openSet A.powered T)
    (i : I) (P : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)))
    (hp : IsInvDomain (n+1) P) (hPN : P.N = univ) (hPE : P.E = [])
    (d : ℕ) (hd : 1 < d) (hPd : P.d ≤ d)
    (f : ι → A.openSet i → ℂ)
    (hf : ∀ j, MDifferentiable 𝓘(ℂ, ComplexModel (n+1)) 𝓘(ℂ, ℂ) (f j)) :
    let weight : ι → ℕ := fun _ => d
    let R : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)) := ⟨univ,[],finiteFunctionIdeal f,d⟩
    IsInvDomain (n+1) R →
    A.record i = ⟨univ,[],weightedFunctionIdeal weight f,weightedCommonMark weight⟩ →
    NonmonomialOrderLocal.nmPart P = R.ideal →
    IsCanonical P ((CanonicalCentres.canonicalInvariant (n+1)).inv P)
      (BlowupTowerTransforms.restrict (A.openSet i) T) := by
  intro weight R hr hRaw hResid
  have hQN : (A.record i).N = univ := congrArg MarkedIdeal.N hRaw
  have hQE : (A.record i).E = [] := congrArg MarkedIdeal.E hRaw
  have hQd : 1 < (A.record i).d := by
    rw [hRaw]
    change 1 < weightedCommonMark weight
    let j : ι := Classical.choice inferInstance
    have hE := compressionExponent_pos weight (fun _ => Nat.zero_lt_of_lt hd) j
    have hm := weight_mul_compressionExponent weight j
    change d * (weightedCommonMark weight / d) = weightedCommonMark weight at hm
    change 0 < weightedCommonMark weight / d at hE
    have hLE := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hE)
    rw [Nat.mul_one,hm] at hLE
    exact hd.trans_le hLE
  have hQDom := A.domain i
  rw [hRaw] at hQDom
  have hCl : LocWPEquiv R (A.record i) := by
    rw [hRaw]
    exact equal_weight_native_functions_locWPEquiv (X := CMfd.of (n := n+1) (A.openSet i))
      f hf d (Nat.zero_lt_of_lt hd) [] hr hQDom
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
    hPE hPd hResid hCl.symm (by simp [hQE]) hActive

end
end Hironaka.HironakaG8FinitePowerReductionLocalEquiv
