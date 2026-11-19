import Hironaka.Resolution.HironakaActualProjectionVerticalOrder
import Hironaka.Resolution.HironakaSharpActualProductNewExceptionalFactor
import Hironaka.Blowup.GlueingTrivialAction

/-! WHOLE native TOTAL-created divisor factors in a GIVEN inherited chart
chain. The primitive chain stores no ideal/order/cosupport/presentation
field. No arbitrary-q history or continued testhood is constructed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualInheritedVerticalTotalFactor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates BlowupMonomialCharts BlowupSNCTransform
  BlowupStrictSubmanifold RelativePrincipalizationSpan InvertibleIdealQuotient
  BlowupControlledTransform NormalCrossings
  IdealWeightPowers GermIdealOrder MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupExceptionalDivisor BlowupFunctionTransform MemberPullback
  HironakaSharpOriginalMemberProduct
  HironakaSharpActualProductNewExceptionalFactor HironakaActualProjectionVerticalOrder

/-- ONLY primitive actual atlas, singleton, flattening and full native/inherited
coordinate identities along the GIVEN tower. No ideal or order field occurs. -/
def InheritedLastChartChain {n : ℕ} {X : CMfd.{u} (n+1)} :
    {Y : CMfd.{u} (n+1)} → (T : BlowupTower X Y) →
      OpenPartialHomeomorph Y (ComplexModel (n+1)) → Prop
  | _,.refl,e => e∈atlas (ComplexModel (n+1)) X
  | _,.step T C π _,e' =>
      e'∈atlas (ComplexModel (n+1)) _ ∧
      ∃(e : OpenPartialHomeomorph _ (ComplexModel (n+1))) (x : _)
        (Φ : LocalHolomorphicEquivAt (n:=n+1) (chartAt (ComplexModel (n+1)) x x)),
        InheritedLastChartChain T e ∧ C={x} ∧ x∈e.source ∧ e x=0 ∧
        Φ.source⊆(chartAt (ComplexModel (n+1)) x).target ∧
        (∀{y},y∈(chartAt (ComplexModel (n+1)) x).source →
          chartAt (ComplexModel (n+1)) x y∈Φ.source →
          (y∈C ↔ Φ.toFun (chartAt (ComplexModel (n+1)) x y)∈complexCoordinatePlane (n+1) 0)) ∧
        (∀v∈e'.source,π v∈e.source ∧ e (π v)=monomial 0 (Fin.last n) (e' v)) ∧
        (∀v∈e'.source,π v∈flatDomain Φ ∧
          monomial 0 (Fin.last n) (e' v)=Φ.toFun (chartAt (ComplexModel (n+1)) x (π v)))

private theorem chain_atlas {n : ℕ} {X Y : CMfd.{u} (n+1)} (T : BlowupTower X Y)
    (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) (h : InheritedLastChartChain T e) :
    e∈atlas (ComplexModel (n+1)) Y := by
  cases T with
  | refl => exact h
  | step T C π hπ => exact h.1

private theorem chart_smooth {r : ℕ} {X : CMfd.{u} r}
    (e : OpenPartialHomeomorph X (ComplexModel r)) (he : e∈atlas (ComplexModel r) X) :
    ∀z∈e.source,ContMDiffAt 𝓘(ℂ,ComplexModel r) 𝓘(ℂ,ComplexModel r) ∞ e z := by
  have hmax := IsManifold.subset_maximalAtlas (I:=𝓘(ℂ,ComplexModel r)) (n:=∞) he
  intro z hz
  exact (contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt (e.open_source.mem_nhds hz)

private theorem chart_coordinate_holomorphic {r : ℕ} {X : CMfd.{u} r}
    (e : OpenPartialHomeomorph X (ComplexModel r)) (he : e∈atlas (ComplexModel r) X)
    (j : Fin r) {z : X} (hz : z∈e.source) : HolomorphicAt r (fun v=>e v j) z := by
  filter_upwards [e.open_source.mem_nhds hz] with v hv
  exact ((EuclideanSpace.proj j : ComplexModel r →L[ℂ] ℂ).differentiableAt.mdifferentiableAt).comp v
    ((chart_smooth e he v hv).mdifferentiableAt (by simp))

/-- BOTH whole member directions of the TOTAL-created divisor, at every
point of the given chart and for every function/multiplier germ. -/
theorem inherited_total_divisor_mem_iff {n : ℕ} {X : CMfd.{u} (n+1)} :
    {Y : CMfd.{u} (n+1)} → (T : BlowupTower X Y) →
      (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) → InheritedLastChartChain T e →
      ∀z∈e.source,∀g : Y→ℂ,
        (BlowupTowerTransforms.exceptionalDivisor T).ideal.mem z g ↔
          IsInSpanAt (n:=n+1) (·=fun v=>e v (Fin.last n)^T.length) z g
  | _,.refl,e,_,z,_,g => by
      rw [BlowupTowerTransforms.exceptionalDivisor_refl_ideal]
      have hfun : (fun v=>e v (Fin.last n)^(BlowupTower.refl : BlowupTower X X).length)=
          (1 : X→ℂ) := by
        funext v
        simp
      rw [hfun]
      exact unit_mem_iff_principal g
  | _,.step T C π hπ,e',h,z,hz,g => by
      obtain ⟨he',e,x,Φ,hchain,hC,hx,h0,hsrc,hflat,hInherited,hNative⟩ := h
      have he := chain_atlas T e hchain
      have hτ := chart_coordinate_holomorphic e' he' (Fin.last n) hz
      have hBorn := GlueingTrivialAction.isLocalEquation_monomial hπ hsrc hflat
        (Nat.zero_le (Fin.last n).val) e'.open_source (chart_smooth e' he') hNative
      have hPull (f : _→ℂ) :
          (GermIdeal.pullback (m:=n+1) π (BlowupTowerTransforms.exceptionalDivisor T).ideal).mem z f ↔
            IsInSpanAt (n:=n+1) (·=fun v=>e' v (Fin.last n)^T.length) z f := by
        have hh := MemberPullback.pullback_mem_iff_of_generator hπ.contMDiff
          (𝔞:=(BlowupTowerTransforms.exceptionalDivisor T).ideal) (z:=z)
          (h:=fun v=>e v (Fin.last n)^T.length)
          (holomorphicAt_pow (chart_coordinate_holomorphic e he (Fin.last n) (hInherited z hz).1) _)
          (inherited_total_divisor_mem_iff T e hchain (π z) (hInherited z hz).1) f
        apply hh.trans
        apply MemberPullback.isInSpanAt_eq_congr
        filter_upwards [e'.open_source.mem_nhds hz] with v hv
        change e (π v) (Fin.last n)^T.length=e' v (Fin.last n)^T.length
        rw [(hInherited v hv).2]
        simp [monomial_apply]
      rw [BlowupTowerTransforms.exceptionalDivisor_step_ideal]
      have hh := mul_mem_iff_principal (holomorphicAt_pow hτ T.length) hτ hPull
        (hBorn.generates z hz) g
      have hfun : (fun v=>e' v (Fin.last n)^T.length)*(fun v=>e' v (Fin.last n))=
          (fun v=>e' v (Fin.last n)^(BlowupTower.step T C π hπ).length) := by
        funext v
        simp only [Pi.mul_apply,BlowupTower.length_step,pow_succ]
      rw [hfun] at hh
      exact hh

/-- Every genuine power of the native TOTAL factor, including original mark0. -/
theorem inherited_total_divisor_power_mem_iff {n : ℕ} {X Y : CMfd.{u} (n+1)}
    (T : BlowupTower X Y) (e : OpenPartialHomeomorph Y (ComplexModel (n+1)))
    (hchain : InheritedLastChartChain T e) (d : ℕ) (z : Y) (hz : z∈e.source) (g : Y→ℂ) :
    (idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal d).mem z g ↔
      IsInSpanAt (n:=n+1) (·=fun v=>e v (Fin.last n)^(T.length*d)) z g := by
  have hh := idealPow_principal_mem_iff
    (holomorphicAt_pow (chart_coordinate_holomorphic e (chain_atlas T e hchain) (Fin.last n) hz) T.length)
    (inherited_total_divisor_mem_iff T e hchain z hz) d g
  have hfun : (fun v=>e v (Fin.last n)^T.length)^d=(fun v=>e v (Fin.last n)^(T.length*d)) := by
    funext v
    exact (pow_mul _ _ _).symm
  rwa [hfun] at hh

private theorem order_of_sharp {r : ℕ} {Y : CMfd.{u} r} (W : Set Y) (I : GermIdeal r Y)
    (z : Y) (a : ℕ) (hI : ∀g,I.mem z g→HolomorphicAt r g z)
    (hGood : z∈cosupport r W I a) (hBad : z∉cosupport r W I (a+1)) :
    GermIdealOrder.order r W I z=(a : ℕ∞) := by
  apply le_antisymm
  · apply ENat.lt_natCast_add_one_iff.mp
    apply lt_of_not_ge
    intro h
    apply hBad
    exact ⟨hGood.1,(le_order_iff hI).mp (by simpa only [Nat.cast_add,Nat.cast_one] using h)⟩
  · exact (le_order_iff hI).mpr hGood.2

private theorem sharp_at_origin {n : ℕ} {X Y : CMfd.{u} (n+1)}
    (M : MarkedIdeal (n+1) X) (hN : IsClosedSubmanifold (n+1) M.N)
    (hI : M.ideal.IsCoherent) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) (hchain : InheritedLastChartChain T e)
    (z : Y) (hz : z∈e.source) (hzN : z∈(M.geoTransformAlong T).N) (he0 : e z=0) :
    let F := idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d
    z∈cosupport (n+1) (M.geoTransformAlong T).N F (T.length*M.d) ∧
      z∉cosupport (n+1) (M.geoTransformAlong T).N F (T.length*M.d+1) := by
  cases T with
  | refl =>
    dsimp only
    simp only [BlowupTowerTransforms.exceptionalDivisor_refl_ideal,idealPow_unitIdeal,
      BlowupTower.length_refl,Nat.zero_mul,Nat.zero_add]
    refine ⟨⟨hzN,orderGE_zero (fun _ h=>h)⟩,?_⟩
    rw [cosupport_unitIdeal (Nat.le_refl 1)]
    simp
  | step T C π hπ =>
    dsimp only
    obtain ⟨he',eold,x,Φ,hprev,hC,hx,h0,hsrc,hflat,hInherited,hNative⟩ := hchain
    have hBorn := GlueingTrivialAction.isLocalEquation_monomial hπ hsrc hflat
      (Nat.zero_le (Fin.last n).val) e.open_source (chart_smooth e he') hNative
    have hzC : π z∈C := by
      apply (hflat (hNative z hz).1.1 (hNative z hz).1.2).mpr
      rw [←(hNative z hz).2,he0]
      intro i hi
      simp [monomial_apply]
    have hPrev := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hT.1
    have hCN : C⊆(M.geoTransformAlong T).N := fun v hv => (hT.2.2.1 hv).1
    have hSharp := exceptional_power_order_at_strict hπ hPrev.1 hCN z hzN hzC
      ((BlowupTower.step T C π hπ).length*M.d)
    have hWhole (g : _→ℂ) :
        (idealPow (BlowupTowerTransforms.exceptionalDivisor (.step T C π hπ)).ideal M.d).mem z g ↔
        (idealPow (GermIdeal.pullback (m:=n+1) π (vanishingIdeal (n:=n+1) C))
          ((BlowupTower.step T C π hπ).length*M.d)).mem z g := by
      exact (inherited_total_divisor_power_mem_iff (.step T C π hπ) e
        ⟨he',eold,x,Φ,hprev,hC,hx,h0,hsrc,hflat,hInherited,hNative⟩ M.d z hz g).trans
          (hBorn.idealPow_mem_iff _ z hz g).symm
    constructor
    · exact ⟨hzN,fun g hg=>hSharp.1.2 g ((hWhole g).mp hg)⟩
    · intro h
      exact hSharp.2.1 ⟨hzN,fun g hg=>h.2 g ((hWhole g).mpr hg)⟩

/-- Actual masks derive the carrier point, then ordinary native geometry
derives sharp factor order and ALL cuts, with literal original mark/E clocks. -/
theorem inherited_total_divisor_power_order {n : ℕ} {X Y : CMfd.{u} (n+1)}
    (M : MarkedIdeal (n+1) X) (hN : IsClosedSubmanifold (n+1) M.N)
    (hI : M.ideal.IsCoherent) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (e : OpenPartialHomeomorph Y (ComplexModel (n+1))) (hchain : InheritedLastChartChain T e)
    (SN : Finset (Fin (n+1))) (hSN : Fin.last n∉SN)
    (hflat : ∀v∈e.source,v∈(M.geoTransformAlong T).N ↔
      Fin.last n∉SN ∧ e v∈coordSubspace SN)
    (z : Y) (hz : z∈e.source) (he0 : e z=0) :
    let Q := M.geoTransformAlong T
    let F := idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d
    z∈Q.N ∧ Q.d=M.d ∧ Q.E.length=M.E.length+T.length ∧
      z∈cosupport (n+1) Q.N F (T.length*M.d) ∧
      z∉cosupport (n+1) Q.N F (T.length*M.d+1) ∧
      GermIdealOrder.order (n+1) Q.N F z=(T.length*M.d : ℕ∞) ∧
      ∀k : ℕ,z∈cosupport (n+1) Q.N F k ↔ k≤T.length*M.d := by
  dsimp only
  have hzN : z∈(M.geoTransformAlong T).N := (hflat z hz).mpr ⟨hSN,by
    rw [he0]
    intro i hi
    rfl⟩
  obtain ⟨hGood,hBad⟩ := sharp_at_origin M hN hI T hT e hchain z hz hzN he0
  have hHol : ∀g,(idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal M.d).mem z g →
      HolomorphicAt (n+1) g z := fun _ h=>GermIdealOrder.holomorphicAt_of_mem_idealPow h
  have hOrder := order_of_sharp _ _ z (T.length*M.d) hHol hGood hBad
  refine ⟨hzN,d_geoTransformAlong M T,length_E_geoTransformAlong M T,hGood,hBad,hOrder,?_⟩
  intro k
  constructor
  · intro h
    have hh := (le_order_iff hHol).mpr h.2
    rw [hOrder] at hh
    exact_mod_cast hh
  · intro h
    refine ⟨hzN,(le_order_iff hHol).mp ?_⟩
    rw [hOrder]
    exact_mod_cast h

end
end Hironaka.HironakaActualInheritedVerticalTotalFactor
