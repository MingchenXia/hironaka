import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers
import Hironaka.Resolution.HironakaActualWeightedCoefficientCompression
import Hironaka.Resolution.HironakaActualFixedInheritedSelector
import Hironaka.Resolution.HironakaActualNormalZeroAnalyticSaturation
import Hironaka.Resolution.HironakaG8SameHSCuspContact
import Hironaka.Resolution.HironakaActualZeroSectionFormalBasis
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-! The actual formal diagram of the embedded cusp in its displayed coordinates. -/
set_option autoImplicit false
open Set
open scoped MonomialOrder
namespace Hironaka.HironakaG8NativeCuspDiagram
noncomputable section

open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualWeightedCoefficientCompression HironakaActualFixedInheritedSelector
  HironakaActualNormalZeroAnalyticSaturation HironakaActualCoefficientPresentationCentrePower
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticBlowupTaylor HironakaActualOriginalFormalTaylor
  HironakaActualFormalInitialDiagram HironakaActualZeroSectionFormalBasis
  HironakaActualReducedFormalStandardBasis HironakaActualAnalyticFormalNormalPowers
  HironakaActualTaylorCoordinateNaturality
  HironakaG8SameHSCuspContact

def cuspSeries (p : ℕ) : MvPowerSeries (Fin 2) ℂ :=
  (MvPowerSeries.X (1 : Fin 2)) ^ 2 - (MvPowerSeries.X (0 : Fin 2)) ^ p

abbrev cuspVertex : Fin 2 →₀ ℕ := Finsupp.single 1 2

theorem cusp_actual_taylor (p : ℕ) :
    actualUnshiftedTaylorAlgHom 2 (cuspGerm p) = cuspSeries p := by
  have hx : tangentPullback 1 1 (normalCoordinate 0 1 0) = normalCoordinate 0 2 0 := by
    unfold tangentPullback normalCoordinate coordinateGerm
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Filter.Eventually.of_forall fun _ => rfl
  change actualUnshiftedTaylorAlgHom 2
    ((normalCoordinate 1 1 0)^2 - (tangentPullback 1 1 (normalCoordinate 0 1 0))^p) = _
  rw [hx, map_sub, map_pow, map_pow,
    show normalCoordinate 1 1 0 = coordinateGerm (1 : Fin 2) from rfl,
    show normalCoordinate 0 2 0 = coordinateGerm (0 : Fin 2) from rfl,
    actualUnshiftedTaylor_coordinate, actualUnshiftedTaylor_coordinate]
  rfl

private theorem cusp_head_coeff (p : ℕ) :
    MvPowerSeries.coeff cuspVertex (cuspSeries p) = 1 := by
  have hne : cuspVertex ≠ Finsupp.single (0 : Fin 2) p := by
    intro h
    have hAt := congrArg (fun b : Fin 2 →₀ ℕ => b (1 : Fin 2)) h
    simp at hAt
  simp [cuspSeries, MvPowerSeries.coeff_X_pow, hne]

private theorem cusp_series_ne_zero (p : ℕ) : cuspSeries p ≠ 0 := by
  intro h
  have hc := cusp_head_coeff p
  rw [h, map_zero] at hc
  exact zero_ne_one hc

theorem cusp_initial_exponent (p : ℕ) (hp : 2 < p) (h : cuspSeries p ≠ 0) :
    actualInitialExponent MonomialOrder.degLex _ h = cuspVertex := by
  apply actualInitialExponent_eq_of_coefficients
  · rw [cusp_head_coeff p]
    exact one_ne_zero
  · intro b hb
    have hy : b ≠ cuspVertex := by
      rintro rfl
      exact lt_irrefl _ hb
    have hx : b ≠ Finsupp.single (0 : Fin 2) p := by
      rintro rfl
      change toDegLex (Finsupp.single (0 : Fin 2) p) <
        toDegLex cuspVertex at hb
      rw [Finsupp.DegLex.lt_iff] at hb
      simp [cuspVertex, hp.ne'] at hb
      omega
    simp [cuspSeries, MvPowerSeries.coeff_X_pow, hy, hx]

theorem cusp_diagram_iff (p : ℕ) (hp : 2 < p) (b : Fin 2 →₀ ℕ) :
    b ∈ actualInitialDiagram MonomialOrder.degLex (Ideal.span {cuspSeries p}) ↔
      cuspVertex ≤ b := by
  have hF := cusp_series_ne_zero p
  constructor
  · rintro ⟨G, hG, hne, he⟩
    obtain ⟨H, rfl⟩ := Ideal.mem_span_singleton.mp hG
    have hH : H ≠ 0 := by
      intro hh
      simp [hh] at hne
    rw [actualInitialExponent_mul _ _ _ hF hH, cusp_initial_exponent p hp hF] at he
    rw [← he]
    exact le_self_add
  · intro hb
    exact actualInitialDiagram_upper _ _ _ _ ⟨cuspSeries p,
      Ideal.subset_span (by simp), hF, cusp_initial_exponent p hp hF⟩ hb


/-- The actual reduced series for the cusp vertex is the complete cusp
polynomial, including its term outside the shared initial diagram. -/
theorem cuspSeries_reduced_vertex (p : ℕ) (hp : 2 < p)
    (a : actualInitialVertices MonomialOrder.degLex (Ideal.span {cuspSeries p})) :
    cuspSeries p = actualReducedVertexSeries MonomialOrder.degLex _ a := by
  classical
  have ha : a.val = cuspVertex := by
    have hm : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.span {cuspSeries p})) a.val := by
      simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.property
    have hle := (cusp_diagram_iff p hp a.val).mp hm.1
    exact le_antisymm (hm.2 ((cusp_diagram_iff p hp _).mpr le_rfl) hle) hle
  apply actualReducedVertexSeries_unique
  · exact Ideal.subset_span (by simp)
  · intro b hb
    have hx : b ≠ Finsupp.single (0 : Fin 2) p := by
      intro he
      have hh := ((cusp_diagram_iff p hp b).mp hb) (1 : Fin 2)
      rw [he] at hh
      simp at hh
    simp [ha, cuspSeries, MvPowerSeries.coeff_X_pow, hx]

/-- Exact whole embedded analytic diagram, with the ordinary cusp cone
and the full normal cone. -/
theorem embedded_cusp_diagram (p : ℕ) (hp : 2 < p)
    (a : Fin 2 →₀ ℕ) (c : Fin 1 →₀ ℕ) :
    actualJoinedExponent a c ∈ actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom 3).toRingHom (embeddedCuspIdeal p)) ↔
      c ≠ 0 ∨ cuspVertex ≤ a := by
  unfold embeddedCuspIdeal
  rw [actualTaylor_zeroSectionIdeal (d := 2) (t := 1), Ideal.map_span, Set.image_singleton,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, cusp_actual_taylor,
    mem_actualInitialDiagram_zeroSection_joined_iff (d := 2) (t := 1), cusp_diagram_iff p hp]


/-- The actual historical label candidates have precisely the degree-one
normal vertex and the degree-two cusp vertex. -/
theorem embedded_cusp_vertices (p : ℕ) (hp : 2 < p) :
    actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom 3).toRingHom (embeddedCuspIdeal p)) =
      {actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ), Finsupp.single (2 : Fin 3) 1} := by
  classical
  let K : Ideal (MvPowerSeries (Fin 2) ℂ) := Ideal.span {cuspSeries p}
  have hK : K ≠ ⊤ := by
    intro h
    have hz : (0 : Fin 2 →₀ ℕ) ∈ actualInitialDiagram MonomialOrder.degLex K := by
      rw [h]
      exact ⟨MvPowerSeries.monomial 0 1, by simp, actualMonomial_ne_zero 0,
        actualInitialExponent_monomial _ _⟩
    have hle := (cusp_diagram_iff p hp 0).mp hz
    have hAt := hle (1 : Fin 2)
    simp at hAt
  have hBase (a : Fin 2 →₀ ℕ) :
      a ∈ actualInitialVertices MonomialOrder.degLex K ↔ a = cuspVertex := by
    simp only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro ha
      have hle := (cusp_diagram_iff p hp a).mp ha.1
      exact le_antisymm (ha.2 ((cusp_diagram_iff p hp _).mpr le_rfl) hle) hle
    · rintro rfl
      exact ⟨(cusp_diagram_iff p hp _).mpr le_rfl,
        fun b hb _ => (cusp_diagram_iff p hp b).mp hb⟩
  unfold embeddedCuspIdeal
  rw [actualTaylor_zeroSectionIdeal (d := 2) (t := 1), Ideal.map_span, Set.image_singleton,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, cusp_actual_taylor]
  change actualInitialVertices MonomialOrder.degLex (formalZeroSectionIdeal 2 1 K) = _
  let e := zeroSectionVertexEquiv (t := 1) K
  let base := zeroSectionLiftVertex (t := 1) K ⟨cuspVertex, (hBase _).mpr rfl⟩
  let normal := zeroSectionNormalVertex K hK (0 : Fin 1)
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hv
    let s : ZeroSectionVertexIndex (t := 1) K := e.symm ⟨v, hv⟩
    have he : zeroSectionVertexMap K s = ⟨v, hv⟩ := e.apply_symm_apply _
    cases hs : s with
    | inl a =>
      left
      rw [hs] at he
      have ha := (hBase a.val).mp a.property
      exact (congrArg Subtype.val he).symm.trans (by simp [zeroSectionVertexMap,
        zeroSectionLiftVertex, ha])
    | inr j =>
      right
      rw [hs] at he
      have hj : j.val = (0 : Fin 1) := Subsingleton.elim _ _
      exact (congrArg Subtype.val he).symm.trans (by simp [zeroSectionVertexMap,
        zeroSectionNormalVertex, hj])
  · rintro (rfl | rfl)
    · exact base.property
    · exact normal.property


private theorem embedded_cusp_lift_label :
    actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ) = Finsupp.single (1 : Fin 3) 2 := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [show actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ) (j.castAdd 1) = cuspVertex j by
      simp [actualJoinedExponent]]
    fin_cases j <;> simp
  · rw [show actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ) (j.natAdd 2) = 0 by
      simp [actualJoinedExponent]]
    fin_cases j; simp

/-- The native clearing mark is exactly two on the actual analytic vertex labels. -/
theorem embedded_cusp_native_mark (p : ℕ) (hp : 2 < p) :
    weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)) => normalExponentDegree v.val) = 2 := by
  unfold analyticZeroTaylorIdeal
  rw [embedded_cusp_vertices p hp, embedded_cusp_lift_label]
  unfold weightedCommonMark
  rw [show (∏ v : ({Finsupp.single (1 : Fin 3) 2, Finsupp.single (2 : Fin 3) 1} :
      Finset (Fin 3 →₀ ℕ)), normalExponentDegree v.val) =
      ∏ v ∈ ({Finsupp.single (1 : Fin 3) 2, Finsupp.single (2 : Fin 3) 1} :
        Finset (Fin 3 →₀ ℕ)), normalExponentDegree v from
    Finset.prod_attach _ _]
  have hne : Finsupp.single (1 : Fin 3) 2 ≠ Finsupp.single (2 : Fin 3) 1 := by
    intro h
    have he := congrArg (fun v : Fin 3 →₀ ℕ => v 1) h
    simp at he
  rw [Finset.prod_insert (by simpa), Finset.prod_singleton]
  simp [normalExponentDegree, Finsupp.single_apply]

/-- The fixed selector uses the normal direction at order one, and the cusp
normal inside the plane at order two. The free cusp coordinate is outside
both blocks. -/
theorem embedded_cusp_selector_blocks (p : ℕ) (hp : 2 < p) :
    let V := actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p))
    fixedSelectorBlock V 1 = {(2 : Fin 3)} ∧ fixedSelectorBlock V 2 = {1, 2} := by
  unfold analyticZeroTaylorIdeal
  rw [embedded_cusp_vertices p hp, embedded_cusp_lift_label]
  constructor <;> ext j <;>
    simp only [fixedSelectorBlock, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      Set.mem_insert_iff, Subtype.exists, Finset.mem_insert, Finset.mem_singleton]
  · constructor
    · rintro ⟨v, rfl | rfl, hv, hj⟩
      · simp [normalExponentDegree, Finsupp.single_apply] at hv
      · by_contra h
        exact hj (Finsupp.single_eq_of_ne h)
    · rintro rfl
      exact ⟨Finsupp.single 2 1, Or.inr rfl, by simp [normalExponentDegree, Finsupp.single_apply],
        by simp⟩
  · constructor
    · rintro ⟨v, rfl | rfl, hv, hj⟩
      · left
        by_contra h
        exact hj (Finsupp.single_eq_of_ne h)
      · right
        by_contra h
        exact hj (Finsupp.single_eq_of_ne h)
    · rintro (rfl | rfl)
      · exact ⟨Finsupp.single 1 2, Or.inl rfl,
          by simp [normalExponentDegree, Finsupp.single_apply], by simp⟩
      · exact ⟨Finsupp.single 2 1, Or.inr rfl,
          by simp [normalExponentDegree, Finsupp.single_apply], by simp⟩


/-- The canonical reduced basis in the actual embedded Taylor ideal consists
of the full lifted cusp series and the literal normal coordinate. -/
theorem embedded_cusp_reduced_series (p : ℕ) (hp : 2 < p) :
    let J := analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)
    ∀ a : actualInitialVertices MonomialOrder.degLex J,
      (a.val = Finsupp.single (1 : Fin 3) 2 ∧
        actualReducedVertexSeries MonomialOrder.degLex J a =
          MvPowerSeries.rename (Fin.castAdd 1) (cuspSeries p)) ∨
      (a.val = Finsupp.single (2 : Fin 3) 1 ∧
        actualReducedVertexSeries MonomialOrder.degLex J a = MvPowerSeries.X (2 : Fin 3)) := by
  unfold analyticZeroTaylorIdeal embeddedCuspIdeal
  rw [actualTaylor_zeroSectionIdeal (d := 2) (t := 1), Ideal.map_span, Set.image_singleton,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, cusp_actual_taylor]
  let K : Ideal (MvPowerSeries (Fin 2) ℂ) := Ideal.span {cuspSeries p}
  change ∀ a : actualInitialVertices MonomialOrder.degLex (formalZeroSectionIdeal 2 1 K), _
  intro a
  let e := zeroSectionVertexEquiv (t := 1) K
  obtain ⟨i, rfl⟩ := e.surjective a
  cases i with
  | inl b =>
    change (let a := zeroSectionLiftVertex (t := 1) K b; _) ∨ _
    have hb : b.val = cuspVertex := by
      have hm : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) b.val := by
        simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using b.property
      have hle := (cusp_diagram_iff p hp b.val).mp hm.1
      exact le_antisymm (hm.2 ((cusp_diagram_iff p hp _).mpr le_rfl) hle) hle
    left
    refine ⟨?_, ?_⟩
    · exact (congrArg (fun v => actualJoinedExponent v (0 : Fin 1 →₀ ℕ)) hb).trans
        embedded_cusp_lift_label
    · change actualReducedVertexSeries MonomialOrder.degLex (formalZeroSectionIdeal 2 1 K)
        (zeroSectionLiftVertex K b) = MvPowerSeries.rename (Fin.castAdd 1) (cuspSeries p)
      rw [actualReducedVertexSeries_zeroSection_lift, ← cuspSeries_reduced_vertex p hp b]
  | inr j =>
    right
    have hj : j.val = (0 : Fin 1) := Subsingleton.elim _ _
    change (Finsupp.single (j.val.natAdd 2) 1 = Finsupp.single (2 : Fin 3) 1) ∧
      actualReducedVertexSeries MonomialOrder.degLex (formalZeroSectionIdeal 2 1 K)
        (zeroSectionNormalVertex K j.property j.val) = MvPowerSeries.X (2 : Fin 3)
    rw [actualReducedVertexSeries_zeroSection_normal, hj]
    exact ⟨rfl, rfl⟩


/-- A genuine reduced standard-basis family at the embedded analytic ideal
compresses exactly to the lifted cusp germ and the square of the normal germ. -/
theorem embedded_cusp_reduced_compression (p : ℕ) (hp : 2 < p) :
    let J := analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)
    let V := actualInitialVertices MonomialOrder.degLex J
    ∀ (Γ : V → HolGerm (ComplexModel 3)),
      (∀ a, actualUnshiftedTaylorAlgHom 3 (Γ a) =
        actualReducedVertexSeries MonomialOrder.degLex J a) →
      weightedCompression (fun a : V => normalExponentDegree a.val) Γ =
        Ideal.span {tangentPullback 2 1 (cuspGerm p), (normalCoordinate 2 1 0)^2} := by
  classical
  intro J V Γ hΓ
  have hMark := embedded_cusp_native_mark p hp
  let g := tangentPullback 2 1 (cuspGerm p)
  let z := normalCoordinate 2 1 0
  have hg : actualUnshiftedTaylorAlgHom 3 g =
      MvPowerSeries.rename (Fin.castAdd 1) (cuspSeries p) := by
    change actualUnshiftedTaylorAlgHom 3 (tangentPullback 2 1 (cuspGerm p)) = _
    exact (DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback 2 1) _).trans
      (congrArg (MvPowerSeries.rename (Fin.castAdd 1)) (cusp_actual_taylor p))
  have hz : actualUnshiftedTaylorAlgHom 3 z = MvPowerSeries.X (2 : Fin 3) :=
    actualUnshiftedTaylor_coordinate 3 2
  have hred := embedded_cusp_reduced_series p hp
  have he (a : V) :
      (a.val = Finsupp.single (1 : Fin 3) 2 ∧ Γ a = g) ∨
      (a.val = Finsupp.single (2 : Fin 3) 1 ∧ Γ a = z) := by
    rcases hred a with ⟨ha, hf⟩ | ⟨ha, hf⟩
    · exact Or.inl ⟨ha, actualUnshiftedTaylorAlgHom_injective 3 ((hΓ a).trans (hf.trans hg.symm))⟩
    · exact Or.inr ⟨ha, actualUnshiftedTaylorAlgHom_injective 3 ((hΓ a).trans (hf.trans hz.symm))⟩
  have hV : V = {Finsupp.single (1 : Fin 3) 2, Finsupp.single (2 : Fin 3) 1} := by
    change actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom 3).toRingHom (embeddedCuspIdeal p)) = _
    rw [embedded_cusp_vertices p hp, embedded_cusp_lift_label]
  have hne : Finsupp.single (1 : Fin 3) 2 ≠ Finsupp.single (2 : Fin 3) 1 := by
    intro h
    have hh := congrArg (fun a : Fin 3 →₀ ℕ => a 1) h
    simp at hh
  unfold weightedCompression
  change weightedCommonMark (fun a : V => normalExponentDegree a.val) = 2 at hMark
  rw [hMark]
  apply congrArg Ideal.span
  ext f
  change (∃ a : V, Γ a ^ (2 / normalExponentDegree a.val) = f) ↔ f ∈ ({g, z^2} : Set _)
  constructor
  · rintro ⟨a, rfl⟩
    rcases he a with ⟨ha, hG⟩ | ⟨ha, hG⟩ <;>
      simp [ha, hG, normalExponentDegree, Finsupp.single_apply]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · let a : V := ⟨Finsupp.single 1 2, by simp [hV]⟩
      rcases he a with ⟨ha, hG⟩ | ⟨ha, _⟩
      · exact ⟨a, by simp [ha, hG, normalExponentDegree, Finsupp.single_apply]⟩
      · exact (hne ha).elim
    · let a : V := ⟨Finsupp.single 2 1, by simp [hV]⟩
      rcases he a with ⟨ha, _⟩ | ⟨ha, hG⟩
      · exact (hne ha.symm).elim
      · exact ⟨a, by simp [ha, hG, normalExponentDegree, Finsupp.single_apply]⟩

end
end Hironaka.HironakaG8NativeCuspDiagram
