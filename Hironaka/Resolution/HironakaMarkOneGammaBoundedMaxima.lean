import Hironaka.Analytic.MonomialCaseLocal
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
import Mathlib.Data.Set.Finite.Lemmas

/-! Source-first mathematics: hironaka-mark-one-gamma-bounded-maxima.tex.
Actual mark-one finite Gamma profiles and genuine current maximum attainment.
No compactness, arbitrary lex-bound inference, finite history or full K1 claim. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaMarkOneGammaBoundedMaxima

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms NormalCrossings MonomialInvariant MonomialCase
  MonomialCaseAlong MonomialStepAlong MonomialCaseLocal MonomialInvariantFunctorialAlong
  RelativePrincipalizationSpan MonomialPartAlong DivisorExponentAlong GermIdealOrder MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealRestrictOpen MarkedIdealBiholomorphism MarkedIdealTowerTransport ResolutionDriver

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem markOne_top_singleton {S I : Finset ℕ} {a : ℕ → ℕ}
    (hSn : S.card ≤ n) (hI : I ∈ feasible S a 1)
    (hTop : ∀ K ∈ feasible S a 1,key n a K ≤ key n a I) :
    ∃ i ∈ S,0<a i ∧ I={i} := by
  have hPositive : ∃ i ∈ I,0<a i := by
    by_contra hnot
    have hZero : ∑ i ∈ I,a i=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hnp : ¬0<a i := fun hp => hnot ⟨i,hi,hp⟩
      omega
    have hh := (mem_feasible.mp hI).2
    omega
  obtain ⟨i,hi,hai⟩ := hPositive
  have hiS : i ∈ S := (mem_feasible.mp hI).1 hi
  have hOne : ({i} : Finset ℕ) ∈ feasible S a 1 :=
    mem_feasible.mpr ⟨Finset.singleton_subset_iff.mpr hiS,by simp only [Finset.sum_singleton];omega⟩
  have hCard := card_le_of_top hSn hI hTop hOne
  have heq : ({i} : Finset ℕ)=I := Finset.eq_of_subset_of_card_le
    (Finset.singleton_subset_iff.mpr hi) (by simpa using hCard)
  exact ⟨i,hiS,hai,heq.symm⟩

private theorem markOne_top_profile {S : Finset ℕ} {a : ℕ → ℕ}
    (hSn : S.card ≤ n) (hSum : 1 ≤ ∑ i ∈ S,a i) :
    ∃ i ∈ S,0<a i ∧
      inv n S a 1=(key n (fun _ => a i) {i} : WithBot Val) ∧
      ∀ j ∈ S,a j ≤ a i := by
  obtain ⟨I,hI,hInv,hTop⟩ := exists_top (n := n) hSum
  obtain ⟨i,hi,hai,rfl⟩ := markOne_top_singleton hSn hI hTop
  refine ⟨i,hi,hai,?_,?_⟩
  · simpa only [key,Finset.card_singleton,Finset.sum_singleton] using hInv
  · intro j hj
    by_cases hp : 0<a j
    · have hJ : ({j} : Finset ℕ) ∈ feasible S a 1 :=
        mem_feasible.mpr ⟨Finset.singleton_subset_iff.mpr hj,by simp only [Finset.sum_singleton];omega⟩
      have hh := hTop {j} hJ
      simp only [key,Finset.card_singleton,Finset.sum_singleton,
        Prod.Lex.toLex_le_toLex,lt_self_iff_false,true_and,false_or] at hh
      rcases hh with hlt | ⟨heq,_⟩
      · exact hlt.le
      · exact heq.le
    · omega

private theorem singleton_key_bound (v : Val) (hFirst : (ofLex v).1=n-1)
    {b i : ℕ} (hb : key n (fun _ => b) {i} ≤ v) : b ≤ (ofLex (ofLex v).2).1 := by
  have hPair := Prod.Lex.le_iff.mp hb
  simp only [key,Finset.card_singleton,Finset.sum_singleton] at hPair
  rcases hPair with hlt | ⟨_,hTail⟩
  · rw [hFirst] at hlt
    exact False.elim (lt_irrefl _ hlt)
  · exact Prod.Lex.monotone_fst _ _ hTail

private theorem actual_markOne_profile (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) (hd : M.d=1)
    {x : X} (hx : x ∈ M.cosupp) :
    ∃ i : Fin M.E.length,x ∈ M.E.get i ∧
      0<divExpAlong n M.N M.ideal (M.E.get i) x ∧
      gammaAlong n M.N M.ideal M.E M.d x=
        (key n (fun _ => divExpAlong n M.N M.ideal (M.E.get i) x) {i.val} : WithBot Val) ∧
      ∀ j : Fin M.E.length,x ∈ M.E.get j →
        divExpAlong n M.N M.ideal (M.E.get j) x ≤ divExpAlong n M.N M.ideal (M.E.get i) x := by
  have hxN := M.cosupp_subset_N hx
  have hSum := (mem_cosupport_iff_of_isMonomialAlong hn hM.isClosedSubmanifold_N
    hM.isSNCDivisor hM.isTransverse hM.isCoherent hne hmono M.d hxN).mp hx
  rw [hd] at hSum
  obtain ⟨i,hi,hpos,hInv,hAll⟩ := markOne_top_profile (card_memberIdx_le M.E hM.isSNCDivisor x) hSum
  obtain ⟨hlt,hxi⟩ := (mem_memberIdx M.E).mp hi
  let a : Fin M.E.length := ⟨i,hlt⟩
  have hExp : expDataAlong n M.N M.ideal M.E x i=divExpAlong n M.N M.ideal (M.E.get a) x := by
    simp [expDataAlong,a,hlt]
  refine ⟨a,hxi,?_,?_,?_⟩
  · rwa [hExp] at hpos
  · change inv n (memberIdx M.E x) (expDataAlong n M.N M.ideal M.E x) M.d=_
    rw [hd]
    simpa only [hExp] using hInv
  · intro j hj
    have hh := hAll j.val ((mem_memberIdx M.E).mpr ⟨j.isLt,hj⟩)
    rw [hExp] at hh
    simpa only [expDataAlong,dif_pos j.isLt] using hh

/-- Incident exponent bounds shape Gamma for an arbitrary mark-one ideal,
even before its nonmonomial part has been eliminated. -/
theorem markOne_gamma_bound_on_of_incident_exponents (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hd : M.d=1) (S : Set X) (B : ℕ)
    (hExp : ∀ x ∈ S,x ∈ M.cosupp → ∀ i : Fin M.E.length,x ∈ M.E.get i →
      divExpAlong n M.N M.ideal (M.E.get i) x ≤ B) :
    ∃ v : Val, (ofLex v).1=n-1 ∧
      ∀ x ∈ S,x ∈ M.cosupp → gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot Val) := by
  let v : Val := key n (fun _ => B+1) {0}
  refine ⟨v,by simp [v,key],?_⟩
  intro x hxS hx
  by_cases hSum : 1 ≤ ∑ i ∈ memberIdx M.E x,expDataAlong n M.N M.ideal M.E x i
  · obtain ⟨i,hi,_hpos,hInv,_hAll⟩ := markOne_top_profile (card_memberIdx_le M.E hM.isSNCDivisor x) hSum
    obtain ⟨hlt,hxi⟩ := (mem_memberIdx M.E).mp hi
    let a : Fin M.E.length := ⟨i,hlt⟩
    have hVal : gammaAlong n M.N M.ideal M.E M.d x =
        (key n (fun _ => divExpAlong n M.N M.ideal (M.E.get a) x) {i} : WithBot Val) := by
      change inv n (memberIdx M.E x) (expDataAlong n M.N M.ideal M.E x) M.d=_
      rw [hd,hInv]
      simp [expDataAlong,a,hlt]
    rw [hVal]
    apply WithBot.coe_le_coe.mpr
    apply le_of_lt
    apply key_lt_key_iff.mpr
    right
    refine ⟨by simp,Or.inl ?_⟩
    simp only [Finset.sum_singleton]
    exact Nat.lt_succ_of_le (hExp x hxS hx a hxi)
  · have hBot : gammaAlong n M.N M.ideal M.E M.d x=⊥ := by
      change inv n (memberIdx M.E x) (expDataAlong n M.N M.ideal M.E x) M.d=⊥
      rw [hd,inv_eq_bot_iff]
      omega
    rw [hBot]
    exact bot_le




/-- Incident exponent bounds shape Gamma for an arbitrary mark-one ideal,
even before its nonmonomial part has been eliminated. -/
theorem markOne_gamma_bound_without_monomial (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hd : M.d=1) (B : ℕ)
    (hExp : ∀ x ∈ M.cosupp,∀ i : Fin M.E.length,x ∈ M.E.get i →
      divExpAlong n M.N M.ideal (M.E.get i) x ≤ B) :
    ∃ v : Val, (ofLex v).1=n-1 ∧
      ∀ x ∈ M.cosupp,gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot Val) := by
  obtain ⟨v,hv,hBound⟩ := markOne_gamma_bound_on_of_incident_exponents M hM hd Set.univ B
    (fun x _ hx => hExp x hx)
  exact ⟨v,hv,fun x hx => hBound x (Set.mem_univ x) hx⟩

/-- A uniform numerical bound on incident exponents supplies a shaped
source Gamma bound without compactness or future history. -/
theorem markOne_gamma_bound_of_incident_exponents (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) (hd : M.d=1) (B : ℕ)
    (hExp : ∀ x ∈ M.cosupp,∀ i : Fin M.E.length,x ∈ M.E.get i →
      divExpAlong n M.N M.ideal (M.E.get i) x ≤ B) :
    ∃ v : Val, (ofLex v).1=n-1 ∧
      ∀ x ∈ M.cosupp,gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot Val) := by
  have _hne := hne
  have _hmono := hmono
  have _hn := hn
  exact markOne_gamma_bound_without_monomial M hM hd B hExp

/-- A shaped finite native mark-one bound controls every incident exponent,
the ENTIRE current Gamma image is finite, and nonempty cosupport has an
ACTUAL native maximum. No compactness or maximum certificate is an input. -/
theorem markOne_finite_gamma_image_and_maximum (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) (hd : M.d=1)
    (v : Val) (hFirst : (ofLex v).1=n-1)
    (hBound : ∀ x ∈ M.cosupp,gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot Val)) :
    (∀ x ∈ M.cosupp,∀ i : Fin M.E.length,x ∈ M.E.get i →
      divExpAlong n M.N M.ideal (M.E.get i) x ≤ (ofLex (ofLex v).2).1) ∧
    (gammaAlong n M.N M.ideal M.E M.d '' M.cosupp).Finite ∧
    (M.cosupp.Nonempty → (maxLocusA M).Nonempty) := by
  let B := (ofLex (ofLex v).2).1
  have hProfile (x : X) (hx : x ∈ M.cosupp) :
      ∃ (b : Fin (B+1)) (i : Fin M.E.length),
        gammaAlong n M.N M.ideal M.E M.d x=(key n (fun _ => b.val) {i.val} : WithBot Val) ∧
        ∀ j : Fin M.E.length,x ∈ M.E.get j → divExpAlong n M.N M.ideal (M.E.get j) x ≤ B := by
    obtain ⟨i,_hi,_hpos,hGamma,hAll⟩ := actual_markOne_profile hn M hM hne hmono hd hx
    have hTopBound := hBound x hx
    rw [hGamma] at hTopBound
    have hb : divExpAlong n M.N M.ideal (M.E.get i) x ≤ B :=
      singleton_key_bound v hFirst (WithBot.coe_le_coe.mp hTopBound)
    exact ⟨⟨_,Nat.lt_succ_of_le hb⟩,i,hGamma,fun j hj => (hAll j hj).trans hb⟩
  have hFinite : (gammaAlong n M.N M.ideal M.E M.d '' M.cosupp).Finite := by
    apply (Set.finite_range (fun p : Fin (B+1) × Fin M.E.length =>
      (key n (fun _ => p.1.val) {p.2.val} : WithBot Val))).subset
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨b,i,hGamma,_hAll⟩ := hProfile x hx
    exact ⟨(b,i),hGamma.symm⟩
  refine ⟨?_,hFinite,?_⟩
  · intro x hx i hi
    obtain ⟨_b,_j,_hGamma,hAll⟩ := hProfile x hx
    exact hAll i hi
  · intro hNonempty
    obtain ⟨m,hm,hMax⟩ := Set.exists_max_image _ id hFinite (hNonempty.image _)
    obtain ⟨x,hx,rfl⟩ := hm
    exact ⟨x,hx,fun y hy => hMax _ ⟨y,hy,rfl⟩⟩

private theorem prefix_geometry_and_bound (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E)
    (v : WithBot Val)
    (hBound : ∀ x ∈ M.cosupp,gammaAlong n M.N M.ideal M.E M.d x ≤ v) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsCanonicalSegment M (fun {Q} R => towerInvAlong M (Y := Q) R) T →
      IsGeoTestTower M T ∧
      (geoTransformAlong M T).IsWellFormed ∧
      (∀ y ∈ (geoTransformAlong M T).N,
        IsNonzeroAlongAt (geoTransformAlong M T).N (geoTransformAlong M T).ideal y) ∧
      IsMonomialAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
        (geoTransformAlong M T).E ∧
      ∀ y ∈ (geoTransformAlong M T).cosupp,towerInvAlong M T y ≤ v
  | _,.refl,_hCan => ⟨trivial,hM,hne,hmono,hBound⟩
  | _,.step T C π hπ,hCan => by
      obtain ⟨hPrev,hNonempty,hCentre⟩ := hCan
      obtain ⟨hTest,hCurrent,hNZ,hMono,hBoundT⟩ :=
        prefix_geometry_and_bound hn M hM hne hmono v hBound T hPrev
      subst hCentre
      have hAdm := isAdmissibleCentre_maxLocusA hn hCurrent hNZ hMono
      obtain ⟨hNew,hNewNZ,hNewMono,_hOver,_hOff,hDrop⟩ :=
        monomial_step_along hn hCurrent hNZ hMono hπ
      refine ⟨⟨hTest,hAdm⟩,hNew,hNewNZ,hNewMono,?_⟩
      intro y hy
      obtain ⟨x,hx⟩ := hNonempty
      exact (hDrop x hx y hy).le.trans (hBoundT x hx.1)

/-- The SAME actual native CAN prefix internally retains ordinary geometry,
testness, the original mark one and shaped bound, hence finite current
Gamma image and genuine maximum attainment whenever current cosupport is
nonempty. No current maximum or future history is a premise. -/
theorem canonical_prefix_markOne_bounded_maxima (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) (hd : M.d=1)
    (v : Val) (hFirst : (ofLex v).1=n-1)
    (hBound : ∀ x ∈ M.cosupp,gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot Val))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hCan : IsCanonicalSegment M (fun {Q} R => towerInvAlong M (Y := Q) R) T) :
    let MT := geoTransformAlong M T
    IsGeoTestTower M T ∧ MT.d=1 ∧ MT.IsWellFormed ∧
      (∀ y ∈ MT.N,IsNonzeroAlongAt MT.N MT.ideal y) ∧
      IsMonomialAlong n MT.N MT.ideal MT.E ∧
      (∀ y ∈ MT.cosupp,towerInvAlong M T y ≤ (v : WithBot Val)) ∧
      (∀ y ∈ MT.cosupp,∀ i : Fin MT.E.length,y ∈ MT.E.get i →
        divExpAlong n MT.N MT.ideal (MT.E.get i) y ≤ (ofLex (ofLex v).2).1) ∧
      (gammaAlong n MT.N MT.ideal MT.E MT.d '' MT.cosupp).Finite ∧
      (MT.cosupp.Nonempty → (maxLocusA MT).Nonempty) := by
  obtain ⟨hTest,hCurrent,hNZ,hMono,hBoundT⟩ :=
    prefix_geometry_and_bound hn M hM hne hmono (v : WithBot Val) hBound T hCan
  have hdT : (geoTransformAlong M T).d=1 := by rw [d_geoTransformAlong,hd]
  obtain ⟨hExponents,hFinite,hMax⟩ := markOne_finite_gamma_image_and_maximum hn
    (geoTransformAlong M T) hCurrent hNZ hMono hdT v hFirst hBoundT
  exact ⟨hTest,hdT,hCurrent,hNZ,hMono,hBoundT,hExponents,hFinite,hMax⟩

/-- Ordinary source mark-one geometry INTERNALLY supplies an actual open
and the honest shaped finite Gamma bound under which every GIVEN native
CAN prefix has genuine current maximum attainment, without compactness. -/
theorem exists_open_all_canonical_markOne_prefix_maxima (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) (hd : M.d=1)
    {x : X} (hx : x ∈ M.cosupp) (O : Opens X) (hxO : x ∈ O) :
    ∃ (U : Opens X) (hxU : x ∈ U),(U : Set X) ⊆ O ∧
      ∃ v : Val,gammaAlong n M.N M.ideal M.E M.d x=(v : WithBot Val) ∧
        (ofLex v).1=n-1 ∧
        let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
        MU.d=1 ∧ MU.IsWellFormed ∧
        (∀ y ∈ MU.N,IsNonzeroAlongAt MU.N MU.ideal y) ∧
        IsMonomialAlong n MU.N MU.ideal MU.E ∧
        (⟨x,hxU⟩ : U) ∈ MU.cosupp ∧
        (∀ y : U,gammaAlong n MU.N MU.ideal MU.E MU.d y=
          gammaAlong n M.N M.ideal M.E M.d y.val) ∧
        (∀ y ∈ MU.cosupp,gammaAlong n MU.N MU.ideal MU.E MU.d y ≤ (v : WithBot Val)) ∧
        ∀ {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) U) Y),
          IsCanonicalSegment MU (fun {Q} R => towerInvAlong MU (Y := Q) R) T →
          let MT := geoTransformAlong MU T
          IsGeoTestTower MU T ∧ MT.d=1 ∧ MT.IsWellFormed ∧
            (∀ y ∈ MT.N,IsNonzeroAlongAt MT.N MT.ideal y) ∧
            IsMonomialAlong n MT.N MT.ideal MT.E ∧
            (∀ y ∈ MT.cosupp,towerInvAlong MU T y ≤ (v : WithBot Val)) ∧
            (∀ y ∈ MT.cosupp,∀ i : Fin MT.E.length,y ∈ MT.E.get i →
              divExpAlong n MT.N MT.ideal (MT.E.get i) y ≤ (ofLex (ofLex v).2).1) ∧
            (gammaAlong n MT.N MT.ideal MT.E MT.d '' MT.cosupp).Finite ∧
            (MT.cosupp.Nonempty → (maxLocusA MT).Nonempty) := by
  obtain ⟨i,_hi,_hPositive,hGammaSource,_hAll⟩ := actual_markOne_profile hn M hM hne hmono hd hx
  let v : Val := key n (fun _ => divExpAlong n M.N M.ideal (M.E.get i) x) {i.val}
  have hFirst : (ofLex v).1=n-1 := by simp [v,key]
  have hUpper := eventually_gammaAlong_le hn hM.isClosedSubmanifold_N hM.isSNCDivisor
    hM.isTransverse hM.isCoherent hne M.d (M.cosupp_subset_N hx)
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hUpper
  let U : Opens X := ⟨V ∩ O,hVo.inter O.isOpen⟩
  have hxU : x ∈ U := ⟨hxV,hxO⟩
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  have hMU : MU.IsWellFormed := IsWellFormed.pullback_val hM U
  have hNZ : ∀ y ∈ MU.N,IsNonzeroAlongAt MU.N MU.ideal y :=
    isNonzeroAlongAt_pullback_val hM.isCoherent hne U
  have hMono : IsMonomialAlong n MU.N MU.ideal MU.E :=
    isMonomialAlong_pullback_val_of_isMonomialAlong hM.isCoherent hmono U
  have hdU : MU.d=1 := hd
  have hHol : ∀ y g,M.ideal.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent hg
  have hGamma (y : U) : gammaAlong n MU.N MU.ideal MU.E MU.d y=
      gammaAlong n M.N M.ideal M.E M.d y.val := gammaAlong_pullback_val M hHol U y M.d
  have hCos : MU.cosupp=(Subtype.val : U → X) ⁻¹' M.cosupp := cosupp_pullback_val M hHol U
  have hxCos : (⟨x,hxU⟩ : U) ∈ MU.cosupp := by rw [hCos];exact hx
  have hBoundU : ∀ y ∈ MU.cosupp,gammaAlong n MU.N MU.ideal MU.E MU.d y ≤ (v : WithBot Val) := by
    intro y hy
    rw [hGamma y,←hGammaSource]
    exact hV y.property.1 (MU.cosupp_subset_N hy)
  refine ⟨U,hxU,fun _ hy => hy.2,v,hGammaSource,hFirst,hdU,hMU,hNZ,hMono,hxCos,hGamma,hBoundU,?_⟩
  intro Y T hCan
  exact canonical_prefix_markOne_bounded_maxima hn MU hMU hNZ hMono hdU v hFirst hBoundU T hCan


end
end Hironaka.HironakaMarkOneGammaBoundedMaxima
