import Hironaka.Resolution.HironakaG4SelectedBornAdmissibility
import Hironaka.MarkedIdeal.GeoTransformWellFormed

set_option autoImplicit false

/-! Actual canonical transformed columns and preservation of genuine monomial inputs.
Blueprint: `hironaka-g4-selected-born-canonical-columns.tex`. -/

open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SelectedBornCanonicalColumns

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings SimultaneousNormalCrossings BlowupFlatCoordinates GiraudAlong
  BlowupStrictSubmanifold BlowupSNCTransform MemberPullback
  MonomialPartAlong MonomialCaseAlong DivisorExponentAlong
  BoundaryCount GermIdealOrder RelativePrincipalizationSpan
  MarkedIdeals MarkedIdeals.MarkedIdeal MonomialStepAlong
  HironakaG4MonomialMaximalContact HironakaMonomialBlowup

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem exists_principal_geoTransform_of_mem (hn : 0 < n)
    {M : MarkedIdeal n X} (hM : M.IsWellFormed)
    (hne : ∀ y ∈ M.N, IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) {C : Set X}
    (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hz : z ∈ (M.geoTransform C π).N) (hzC : π z ∈ C) :
    ∃ a' : Fin (M.geoTransform C π).E.length → ℕ,
      IsPrincipalAlongAt (M.geoTransform C π).N (M.geoTransform C π).ideal
        (M.geoTransform C π).E z a' ∧
      (∀ i (hi : i.val < M.E.length),
        a' i = divExpAlong n M.N M.ideal (M.E.get ⟨i.val, hi⟩) (π z)) ∧
      ∀ i, ¬ i.val < M.E.length → a' i =
        (∑ j ∈ Finset.univ.filter (fun j => π z ∈ M.E.get j ∧
          ∀ᶠ y in 𝓝 (π z), y ∈ C → y ∈ M.E.get j),
          divExpAlong n M.N M.ideal (M.E.get j) (π z)) - M.d := by
  have hxN : π z ∈ M.N := hC.subset_N hzC
  obtain ⟨_k, Φ, σ, hsrc, _h0, _hNflat, _hσk, _hinj, hA, hgen⟩ :=
    isPrincipalAlongAt_of_isMonomialAlong hn hM.isClosedSubmanifold_N hM.isSNCDivisor
      hM.isTransverse hM.isCoherent hne hmono hxN
  have hd := NonmonomialStepAlong.le_sum_divExpAlong_of_subset_cosupport hn
    hM.isClosedSubmanifold_N hM.isSNCDivisor hM.isTransverse hM.isCoherent hne hmono
    hC.2.2 hC.subset_N hC.2.1 hzC
  obtain ⟨k', Θ, σ', a', hs, h0, hN', hσk', hinj', hA', ha', hnew, hgen'⟩ :=
    MonomialBlowupAlongChart.exists_snc_chart_geoTransform_along_of_flat hπ
      hM.isClosedSubmanifold_N hM.isCoherent hC hM.isSNCDivisor hM.isTransverse hz hzC
      (T := Finset.univ.filter fun i => π z ∈ M.E.get i) (by simp)
      (fun i hi _ hy hyΦ => hA i (Finset.mem_filter.mp hi).2 hy hyΦ)
      (fun i => divExpAlong n M.N M.ideal (M.E.get i) (π z)) hgen hd
  exact ⟨a', ⟨k', Θ, σ', hs, h0, hN', hσk', hinj', hA', hgen'⟩, ha', hnew⟩

/-- The actual geometric transform by ANY actual admissible blowup preserves
the true next current well-formed, nonzero and monomial-along-carrier inputs. -/
theorem geoTransform_monomial_inputs (hn : 0 < n) {M : MarkedIdeal n X}
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N, IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) {C : Set X}
    (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π) :
    (M.geoTransform C π).IsWellFormed ∧
      (∀ y ∈ (M.geoTransform C π).N,
        IsNonzeroAlongAt (M.geoTransform C π).N (M.geoTransform C π).ideal y) ∧
      IsMonomialAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal
        (M.geoTransform C π).E := by
  have hM' := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hM hC hπ
  have hP : ∀ z ∈ (M.geoTransform C π).N, IsPrincipalMonomialAlongAt n
      (M.geoTransform C π).N (M.geoTransform C π).ideal (M.geoTransform C π).E z := by
    intro z hz
    by_cases hzC : π z ∈ C
    · obtain ⟨a', hPrincipal, _ha, _hnew⟩ :=
        exists_principal_geoTransform_of_mem hn hM hne hmono hC hπ hz hzC
      exact hPrincipal.isPrincipalMonomialAlongAt
    · exact (isPrincipalAlongAt_geoTransform_of_notMem hn hM hne hmono hπ hz hzC).isPrincipalMonomialAlongAt
  obtain ⟨hne', hmono'⟩ := isNonzeroAlongAt_and_isMonomialAlong_of_principal hn
    hM'.isClosedSubmanifold_N hM'.isSNCDivisor hM'.isTransverse hM'.isCoherent hP
  exact ⟨hM', hne', hmono'⟩

private theorem divExpAlong_zero_of_notMem {N H : Set Y} {I : GermIdeal n Y}
    (hNH : IsClosed (N ∩ H)) {z : Y} (hz : z ∉ H) : divExpAlong n N I H z = 0 := by
  have hnot : ¬ ∃ e, ¬ IsDivNearAlong n N I H (e + 1) z := by
    rintro ⟨e, he⟩
    exact he (isDivNearAlong_of_notMem hNH (fun h => hz h.2) (e + 1))
  rw [divExpAlong, dif_neg hnot]

private theorem canonical_divExpAlong_of_principal
    {N : Set Y} {E : List (Set Y)} {I : GermIdeal n Y} (hN : IsClosed N)
    (hE : ∀ H ∈ E, IsClosed H) (hI : I.IsCoherent) {z : Y} (hz : z ∈ N)
    {a : Fin E.length → ℕ} (hP : IsPrincipalAlongAt N I E z a) (i : Fin E.length) :
    divExpAlong n N I (E.get i) z = if z ∈ E.get i then a i else 0 := by
  by_cases hi : z ∈ E.get i
  · rw [if_pos hi]
    obtain ⟨k, Φ, σ, hsrc, _h0, hNflat, hσk, hinj, hA, hgen⟩ := hP
    exact divExpAlong_eq_of_principal hsrc hNflat
      (fun j hj k hk hjk => hinj (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2 hjk)
      (fun j hj => hσk j (Finset.mem_filter.mp hj).2)
      (fun j hj _ hy hyΦ => hA j (Finset.mem_filter.mp hj).2 hy hyΦ) a
      (eventually_isInSpanOnAt_iff_of_isCoherent hI hgen)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hz
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) hi
  · rw [if_neg hi]
    exact divExpAlong_zero_of_notMem (hN.inter (hE _ (List.get_mem E i))) hi

/-- Every actual canonical transformed column, including all absent old zero
positions, is the literal selected row transform of the original canonical row. -/
theorem canonical_columns_selected_born_geoTransform {M : MarkedIdeal n X}
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N, IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) (S : Finset (Fin M.E.length))
    (hC : M.IsAdmissibleCentre (M.N ∩ memberInter M.E S)) {π : Y → X}
    (hπ : IsBlowupAlong n (M.N ∩ memberInter M.E S) π) {z : Y}
    (hz : z ∈ (M.geoTransform (M.N ∩ memberInter M.E S) π).N)
    (hzC : π z ∈ M.N ∩ memberInter M.E S) :
    let R : Finset (Fin M.E.length) := Finset.univ.filter
      (fun i => z ∈ geoStrictTransform π (M.N ∩ memberInter M.E S) (M.E.get i))
    ∀ j : Fin (M.geoTransform (M.N ∩ memberInter M.E S) π).E.length,
      divExpAlong n (M.geoTransform (M.N ∩ memberInter M.E S) π).N
        (M.geoTransform (M.N ∩ memberInter M.E S) π).ideal
        ((M.geoTransform (M.N ∩ memberInter M.E S) π).E.get j) z =
      transformRow M.d S R (fun i => divExpAlong n M.N M.ideal (M.E.get i) (π z))
        (Fin.cast (length_E_geoTransform M (M.N ∩ memberInter M.E S) π) j) := by
  let C := M.N ∩ memberInter M.E S
  let R : Finset (Fin M.E.length) := Finset.univ.filter
    (fun i => z ∈ geoStrictTransform π C (M.E.get i))
  change ∀ j : Fin (M.geoTransform C π).E.length,
    divExpAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal
      ((M.geoTransform C π).E.get j) z =
    transformRow M.d S R (fun i => divExpAlong n M.N M.ideal (M.E.get i) (π z))
      (Fin.cast (length_E_geoTransform M C π) j)
  have hn : 0 < n := pos_of_isBlowupAlong hπ hzC
  have hM' := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hM hC hπ
  obtain ⟨a', hP, ha, hnew⟩ := exists_principal_geoTransform_of_mem hn hM hne hmono hC hπ hz hzC
  have hfilter := filter_eventually_subset_inter_memberInter_eq hn hM.isSNCDivisor
    hM.isTransverse hzC.1 hzC.2
  intro j
  have hcanon := canonical_divExpAlong_of_principal hM'.isClosedSubmanifold_N.1
    hM'.isSNCDivisor.1 hM'.isCoherent hz hP j
  rw [hcanon]
  have hget : (M.geoTransform C π).E.get j =
      if h : j.val < M.E.length then geoStrictTransform π C (M.E.get ⟨j.val, h⟩)
        else π ⁻¹' C := get_map_append_singleton M.E (geoStrictTransform π C) (π ⁻¹' C) j
  by_cases hj : j.val < M.E.length
  · have hcast : Fin.cast (length_E_geoTransform M C π) j =
        (⟨j.val, hj⟩ : Fin M.E.length).castSucc := Fin.ext rfl
    rw [hget, dif_pos hj, ha j hj, hcast]
    rw [transformRow, Fin.lastCases_castSucc]
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
  · have hjval : j.val = M.E.length := by
      have hlt : j.val < M.E.length + 1 := calc
        j.val < (M.geoTransform C π).E.length := j.isLt
        _ = M.E.length + 1 := length_E_geoTransform M C π
      omega
    have hcast : Fin.cast (length_E_geoTransform M C π) j = Fin.last M.E.length := by
      apply Fin.ext
      exact hjval
    have hzD : z ∈ π ⁻¹' C := hzC
    rw [hget, dif_neg hj, if_pos hzD, hnew j hj, hfilter, hcast]
    rw [transformRow, Fin.lastCases_last]
    rfl

/-- Off the actual centre, every true old canonical column is preserved and
the actual newborn column is zero, with no deleted ordered slots. -/
theorem canonical_columns_geoTransform_of_notMem (hn : 0 < n) {M : MarkedIdeal n X}
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N, IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) {C : Set X}
    (hC : M.IsAdmissibleCentre C) {π : Y → X} (hπ : IsBlowupAlong n C π)
    {z : Y} (hz : z ∈ (M.geoTransform C π).N) (hzC : π z ∉ C) :
    ∀ j : Fin (M.geoTransform C π).E.length,
      divExpAlong n (M.geoTransform C π).N (M.geoTransform C π).ideal
        ((M.geoTransform C π).E.get j) z =
      appendAbsentRow (fun i => divExpAlong n M.N M.ideal (M.E.get i) (π z))
        (Fin.cast (length_E_geoTransform M C π) j) := by
  have hM' := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hM hC hπ
  have hP := isPrincipalAlongAt_geoTransform_of_notMem hn hM hne hmono hπ hz hzC
  intro j
  have hcanon := canonical_divExpAlong_of_principal hM'.isClosedSubmanifold_N.1
    hM'.isSNCDivisor.1 hM'.isCoherent hz hP j
  rw [hcanon]
  by_cases hj : j.val < M.E.length
  · have hcast : Fin.cast (length_E_geoTransform M C π) j =
        (⟨j.val, hj⟩ : Fin M.E.length).castSucc := Fin.ext rfl
    rw [dif_pos hj, hcast]
    simp only [appendAbsentRow, Fin.lastCases_castSucc]
    by_cases hzi : z ∈ (M.geoTransform C π).E.get j
    · rw [if_pos hzi]
    · rw [if_neg hzi]
      have hxi : π z ∉ M.E.get ⟨j.val, hj⟩ := by
        intro hxi
        apply hzi
        exact (MonomialResolution.mem_get_geoTransform_iff_of_notMem hπ M hM.isSNCDivisor hzC j).mpr
          ⟨hj, hxi⟩
      exact (divExpAlong_zero_of_notMem
        (hM.isClosedSubmanifold_N.1.inter (hM.isSNCDivisor.1 _ (List.get_mem M.E _))) hxi).symm
  · have hjval : j.val = M.E.length := by
      have hlt : j.val < M.E.length + 1 := calc
        j.val < (M.geoTransform C π).E.length := j.isLt
        _ = M.E.length + 1 := length_E_geoTransform M C π
      omega
    have hcast : Fin.cast (length_E_geoTransform M C π) j = Fin.last M.E.length := by
      apply Fin.ext
      exact hjval
    rw [dif_neg hj, hcast, ite_self, appendAbsentRow, Fin.lastCases_last]

end

end Hironaka.HironakaG4SelectedBornCanonicalColumns
