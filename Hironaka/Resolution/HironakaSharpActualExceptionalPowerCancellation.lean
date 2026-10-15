/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualRelativeMemberPrime

/-! Genuine all-power exceptional saturation of the actual intrinsic residual.
Real generator/nonzero and no-common-factor geometry precede cancellation.
TOTAL saturation/relative STRICT and chronological histories remain OPEN. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualExceptionalPowerCancellation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualRelativeMemberPrime HironakaSharpOriginalFirstMemberExceptionalFactor
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMemberProduct
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  MonomialPartAlong DivisorExponentAlong NormalCrossings MemberPullback BlowupFlatCoordinates
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers GermIdealOrder
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual free SNC coordinate constructs BOTH real member ideal directions and
nonzero points in EVERY nearby carrier neighborhood. -/
theorem exists_actual_transverse_member_generator (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {x : X} (hx : x ∈ N)
    (i : Fin E.length) (hxi : x ∈ E.get i) :
    ∃ a : X → ℂ,HolomorphicAt n a x ∧
      (∀ g,(vanishingIdeal (n := n) (E.get i)).mem x g ↔ IsInSpanAt (n := n) (·=a) x g) ∧
      ∃ U : Set X,IsOpen U ∧ x ∈ U ∧
        ∀ V : Set X,IsOpen V → V ⊆ U → (V ∩ N).Nonempty → ∃ y ∈ V ∩ N,a y ≠ 0 := by
  obtain ⟨_kC,kN,Φ,σ,hsrc,hσk,_hinj,hflat⟩ :=
    SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn subset_rfl hE hT hT.hasNormalCrossings hx
  have hNflat : ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n kN) :=
    fun hy1 hy2 => (hflat hy1 hy2).2.1
  have hA : ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i)=0) :=
    fun hy1 hy2 => (hflat hy1 hy2).2.2 i hxi
  have hxD := mem_flatDomain_self Φ
  refine ⟨flatCoord Φ (σ i),holomorphicAt_flatCoord Φ (σ i) hxD,
    vanishingIdeal_mem_iff_flatCoord Φ hA hxD,flatDomain Φ,isOpen_flatDomain Φ,hxD,?_⟩
  intro V hVo hVD hVN
  obtain ⟨y,hyV,hyN⟩ := hVN
  have hfreq := frequently_generator_ne_zero hsrc hNflat
    (T := {i}) (fun j hj => by simpa using hσk i hxi) (fun _ => 1) (hVD hyV) hyN
  obtain ⟨z,hz,hzV⟩ := (hfreq.and_eventually (hVo.mem_nhds hyV)).exists
  exact ⟨z,⟨hzV,hz.1⟩,by simpa using hz.2⟩

/-- Real relative prime plus true carrier nonzero cancels the actual member
generator from an ENTIRE relative principal relation. -/
theorem cancel_actual_member_factor (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {x : X} (hx : x ∈ N)
    (i : Fin E.length) (a c : X → ℂ) (ha : HolomorphicAt n a x) (hc : HolomorphicAt n c x)
    (hA : ∀ g,(vanishingIdeal (n := n) (E.get i)).mem x g ↔ IsInSpanAt (n := n) (·=a) x g)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U)
    (hnon : ∀ V : Set X,IsOpen V → V ⊆ U → (V ∩ N).Nonempty → ∃ y ∈ V ∩ N,a y ≠ 0)
    (hnot : ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x c)
    (g : X → ℂ) (hg : HolomorphicAt n g x)
    (hag : IsInSpanOnAt (n := n) N (·=c) x (a*g)) :
    IsInSpanOnAt (n := n) N (·=c) x g := by
  obtain ⟨b,hb,hagbc⟩ := isInSpanOnAt_eq_iff.mp hag
  have haD : (vanishingIdeal (n := n) (E.get i)).mem x a :=
    (hA a).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl ha)
  have hbcD : IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x (c*b) := by
    refine IsInSpanOnAt.congr_right (IsInSpanOnAt.mul_left hg
      (IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self haD ha))) ?_
    filter_upwards [hagbc] with y hy hyN
    change c y*b y=g y*a y
    have hh := hy hyN
    change a y*g y=b y*c y at hh
    exact (mul_comm _ _).trans (hh.symm.trans (mul_comm _ _))
  have hbD := (transverse_member_relative_product_prime hn hE hT hx i c b hc hb hbcD).resolve_left hnot
  have hbA := (restricted_span_iff_principal ha hA b).mp hbD
  obtain ⟨d,hd,hbda⟩ := isInSpanOnAt_eq_iff.mp hbA
  have hcancel : ∀ᶠ y in 𝓝 x,y ∈ N → a y*g y=a y*(d y*c y) := by
    filter_upwards [hagbc,hbda] with y hy hz hyN
    have hh := hy hyN
    change a y*g y=b y*c y at hh
    rw [hh,hz hyN]
    ring
  have heq := eventuallyEq_within_of_mul_eventuallyEq_within hU hnon hxU hg (hd.mul hc) hcancel
  exact isInSpanOnAt_eq_iff.mpr ⟨d,hd,heq⟩

/-- Genuine coherent nonzero total and actual relative principality INTERNALLY
supply the residual's every-member/every-power saturation, in BOTH germ directions. -/
theorem actual_residual_member_power_colon_mem_iff (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {I : GermIdeal n X} (hI : I.IsCoherent) (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y)
    {x : X} (hx : x ∈ N) (f : X → ℂ) (hf : HolomorphicAt n f x)
    (hIgen : ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (i : Fin E.length) (k : ℕ) (g : X → ℂ) :
    (colonAlong n N (nonmonomialPartAlong n N I E) (idealPow (vanishingIdeal (n := n) (E.get i)) k)).mem x g ↔
      (nonmonomialPartAlong n N I E).mem x g := by
  let J := nonmonomialPartAlong n N I E
  obtain ⟨_m,c,_hm,_hmM,hcJ,_hfc,hJgen⟩ := exists_actual_relative_principal_residual hn hN hE hT hI hnz hx f hf hIgen
  have hc : HolomorphicAt n c x := hcJ.1
  have hcollapse (v : X → ℂ) (hv : (restrictOn n N J).mem x v) : J.mem x v :=
    (hJgen v).mpr ⟨hv.1,IsInSpanOnAt.trans (fun s hs => ((hJgen s).mp hs).2) hv.2⟩
  have hJcoh : J.IsCoherent := isCoherent_nonmonomialPartAlong hn hN hE hT hI hnz
  have hpowcoh := GermIdealPullbackCalculus.isCoherent_idealPow
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)) k
  constructor
  · rintro ⟨hg,hcolon⟩
    by_cases hxi : x ∈ E.get i
    · obtain ⟨a,ha,hA,U,hU,hxU,hnon⟩ := exists_actual_transverse_member_generator hn hE hT hx i hxi
      have hnot : ¬IsInSpanOnAt (n := n) N ((vanishingIdeal (n := n) (E.get i)).mem x) x c := by
        intro hcD
        obtain ⟨v,hv,hvnot⟩ := exists_mem_nonmonomialPartAlong_not hn hN hE hT hI hnz hx hxi
        apply hvnot
        exact IsInSpanOnAt.trans (S := (·=c)) (T := (vanishingIdeal (n := n) (E.get i)).mem x) (fun s hs => hs ▸ hcD) ((hJgen v).mp hv).2
      have haD : (vanishingIdeal (n := n) (E.get i)).mem x a :=
        (hA a).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl ha)
      have hpow := MonomialPart.pow_mem_idealPow haD ha k
      have hJpow := hcollapse _ (hcolon _ hpow)
      have hspan : IsInSpanOnAt (n := n) N (·=c) x ((fun y => a y^k)*g) := ((hJgen _).mp hJpow).2
      have hcancel : ∀ t : ℕ,∀ v : X → ℂ,HolomorphicAt n v x →
          IsInSpanOnAt (n := n) N (·=c) x ((fun y => a y^t)*v) →
          IsInSpanOnAt (n := n) N (·=c) x v := by
        intro t
        induction t with
        | zero =>
          intro v _hv hspan
          exact IsInSpanOnAt.congr_right hspan (Eventually.of_forall fun y _ => by simp)
        | succ t ih =>
          intro v hv hspan
          have hspan' : IsInSpanOnAt (n := n) N (·=c) x (a*((fun y => a y^t)*v)) := by
            refine IsInSpanOnAt.congr_right hspan (Eventually.of_forall fun y _ => ?_)
            change a y*(a y^t*v y)=a y^(t+1)*v y
            ring
          exact ih v hv (cancel_actual_member_factor hn hE hT hx i a c ha hc hA hU hxU hnon hnot _ (HolomorphicAt.mul (BlowupFunctionTransform.holomorphicAt_pow ha t) hv) hspan')
      exact (hJgen g).mpr ⟨hg,hcancel k g hg hspan⟩
    · have h1D : (vanishingIdeal (n := n) (E.get i)).mem x (1 : X → ℂ) := by
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [(hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hxi] with y hy hyH
        exact False.elim (hy hyH)
      have h1pow : (idealPow (vanishingIdeal (n := n) (E.get i)) k).mem x (1 : X → ℂ) := by
        change (idealPow (vanishingIdeal (n := n) (E.get i)) k).mem x (fun _ => 1)
        simpa using MonomialPart.pow_mem_idealPow h1D (holomorphicAt_const 1) k
      have hh := hcollapse _ (hcolon _ h1pow)
      convert hh using 1
      funext y
      simp
  · intro hg
    refine ⟨hg.1,fun a ha => ?_⟩
    exact restrictOn_mul_left (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hpowcoh ha)
      (le_restrictOn hJcoh x g hg)

/-- ONLY original inputs construct the SAME real first blowup and every actual
member residual all-power exceptional saturation. -/
theorem exists_actual_original_first_member_residual_power_saturation (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1 ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),IsBlowupAlong n C π ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E) ∧
      ∀ i : Fin E.length,
        let P := memberTotalMarked W (E.get i) C π
        let J := memberExceptionalResidual W (E.get i) C π
        ∀ y ∈ P.N,∀ a : Fin P.E.length,∀ k : ℕ,∀ g : Y → ℂ,
          (colonAlong n P.N J (idealPow (vanishingIdeal (n := n) (P.E.get a)) k)).mem y g ↔ J.mem y g := by
  obtain ⟨C,Y,π,hπ,hCeq,hgeom⟩ := exists_actual_original_first_member_exceptional_factor hn hW hE hd hreg hdense hcompact hne
  refine ⟨C,Y,π,hπ,hCeq,?_⟩
  intro i
  dsimp only
  intro y hy a k g
  obtain ⟨hw,_hTotal,hnz,_hJ,_hnzJ,_hfac,_hnot⟩ := hgeom i
  obtain ⟨f,hf,hgen⟩ := exists_actual_original_member_total_principal hn hE hπ i y
  exact actual_residual_member_power_colon_mem_iff hn hw.isClosedSubmanifold_N hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz hy f hf hgen a k g

end
end Hironaka.HironakaSharpActualExceptionalPowerCancellation
