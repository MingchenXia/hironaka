import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
import Hironaka.Analytic.MonomialCaseLocal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Monomial marked ideals under the blowup of an intersection of members (Hironaka, `hir:monomial-blowup`)

Blueprint `hir:monomial-blowup` (`blueprint/src/hironaka.tex`; TN.5, a remaining open Hironaka node, formalized as stated).
Sources: Bierstone--Milman 2008 (`bierstone-milman08-functoriality`) §5, Włodarczyk 2005 (`wlodarczyk05-hironaka`) Step 2b.

The resolution algorithm only blows up the maximum locus of the monomial invariant (`MonomialStepAlong`); the node is the
statement for an arbitrary feasible set `J` of members through a point `x ∈ N`, i.e. `∑_{H ∈ J} a_H ≥ d`, with centre
`C = N ∩ ⋂_{H ∈ J} H` near `x`:

* the members containing `C` near `x` are exactly those of `J` (`filter_eventually_subset_inter_memberInter_eq`: they are
  distinct coordinate hyperplanes of coordinates adapted to `N`), so the exponent of the exceptional member is
  `∑_{H ∈ J} a_H - d` (TN3's chart `MonomialBlowupAlongChart.exists_snc_chart_geoTransform_along_of_flat`);
* `C` lies in the cosupport near `x` (`eventually_mem_cosupp_of_le_sum`: near `x` the exponents along the members of `J`
  are those at `x`), so it is an admissible centre of the restriction to a neighbourhood `U` of `x`;
* the strict transforms of the members of `J` do not all pass through a point over `C` (TN3's
  `BoundaryCountAlong.card_filter_mem_geoStrictTransform_lt_along`).

## Main results

* `filter_eventually_subset_inter_memberInter_eq`, `eventually_mem_cosupp_of_le_sum`, `divExpAlong_pullback_val_get`;
* `monomial_blowup_of_isAdmissibleCentre`: the transform at a point over the centre, when `C` is admissible on the whole
  manifold;
* **`monomial_blowup`** (`hir:monomial-blowup`): the local statement, on a neighbourhood `U` of `x`.

Import discipline (standalone Hironaka library): the imports are already in the closure of the Hironaka modules; this module
does not import, even transitively, `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaMonomialBlowup

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.BlowupFlatCoordinates Hironaka.DivisorExponentAlong
  Hironaka.MonomialPart Hironaka.MonomialPartAlong
  Hironaka.NormalCrossings Hironaka.BoundaryCount
  Hironaka.MonomialCase Hironaka.MonomialCaseAlong
  Hironaka.BlowupStrictSubmanifold Hironaka.BlowupSNCTransform
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialStepAlong
  Hironaka.GiraudAlong

noncomputable section

variable {n : ℕ}

/-! ### The members containing `N ∩ ⋂_J E_j`, and the cosupport near `x` -/

section Members

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

open Classical in
/-- **The members containing `C = N ∩ ⋂_{j ∈ J} E_j` near a point `x ∈ C` are exactly those of `J`** (`E` simple normal
crossings and transverse to `N`, `0 < n`): in coordinates at `x` adapted to `N` and `E` the
members through `x` are distinct coordinate hyperplanes `{w_{σ i} = 0}` with `σ i` a coordinate of `N`; moving along
`w_{σ i}` for `i ∉ J` stays in `N` and on the members of `J`, and leaves `E_i`. -/
theorem filter_eventually_subset_inter_memberInter_eq (hn : 0 < n) {N : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {J : Finset (Fin E.length)} {x : X}
    (hxN : x ∈ N) (hxJ : ∀ j ∈ J, x ∈ E.get j) :
    Finset.univ.filter (fun i => x ∈ E.get i ∧ ∀ᶠ y in 𝓝 x, y ∈ N ∩ memberInter E J → y ∈ E.get i) = J := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hxi, hCi⟩
    by_contra hi
    obtain ⟨kC, kN, Φ, σ, hΦsrc, hσk, hσinj, hflat⟩ :=
      SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn subset_rfl hE hT hT.hasNormalCrossings hxN
    have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
    obtain ⟨y, ⟨hyD, hyne, hyeq⟩, hyC⟩ :=
      ((frequently_flatMap_ne_zero hΦsrc hxD {σ i}).and_eventually hCi).exists
    have hyN : y ∈ N := by
      refine ((hflat hyD.1 hyD.2).2.1).mpr fun l hl => ?_
      have hli : l ∉ ({σ i} : Finset (Fin n)) := by
        rw [Finset.mem_singleton]
        intro h
        have := hσk i hxi
        rw [← h] at this
        omega
      change flatMap Φ y l = 0
      rw [hyeq l hli]
      exact ((hflat hxD.1 hxD.2).2.1).mp hxN l hl
    have hyI : y ∈ memberInter E J := by
      intro j hj
      have hxj := hxJ j hj
      have hji : σ j ≠ σ i := by
        intro h
        have := hσinj hxj hxi h
        exact hi (this ▸ hj)
      refine ((hflat hyD.1 hyD.2).2.2 j hxj).mpr ?_
      have := hyeq (σ j) (by simpa using hji)
      rw [show Φ.toFun (chartAt (ComplexModel n) x y) (σ j) = flatMap Φ y (σ j) from rfl, this]
      exact ((hflat hxD.1 hxD.2).2.2 j hxj).mp hxj
    exact hyne (σ i) (Finset.mem_singleton_self _) (((hflat hyD.1 hyD.2).2.2 i hxi).mp (hyC ⟨hyN, hyI⟩))
  · intro hi
    exact ⟨hxJ i hi, Eventually.of_forall fun y hy => hy.2 i hi⟩

open Classical in
/-- **`C = N ∩ ⋂_{j ∈ J} E_j` lies in the cosupport near `x`** when `J` is feasible at `x`, `∑_{j ∈ J} e_j(x) ≥ d`, for a
well-formed marked ideal monomial and nonzero along `N` (`0 < n`): near `x` the exponents along the members of `J` are those
at `x`, and a point of `N` lies in the cosupport iff the exponents of the members through it add up to at least `d`. -/
theorem eventually_mem_cosupp_of_le_sum (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (hmono : IsMonomialAlong n 𝔪.N 𝔪.ideal 𝔪.E)
    {J : Finset (Fin 𝔪.E.length)} {x : X} (hxN : x ∈ 𝔪.N) (hxJ : ∀ j ∈ J, x ∈ 𝔪.E.get j)
    (hd : 𝔪.d ≤ ∑ j ∈ J, divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) x) :
    ∀ᶠ y in 𝓝 x, y ∈ 𝔪.N ∩ memberInter 𝔪.E J → y ∈ 𝔪.cosupp := by
  have hexp : ∀ᶠ y in 𝓝 x, ∀ j ∈ J, y ∈ 𝔪.N → y ∈ 𝔪.E.get j →
      divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) y = divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) x :=
    (Finset.eventually_all J).mpr fun j hj => eventually_divExpAlong_get_eq hn h𝔪.isClosedSubmanifold_N
      h𝔪.isSNCDivisor h𝔪.isTransverse h𝔪.isCoherent hne j hxN (hxJ j hj)
  filter_upwards [hexp] with y hy hyC
  show y ∈ cosupport n 𝔪.N 𝔪.ideal 𝔪.d
  refine (mem_cosupport_iff_of_isMonomialAlong hn h𝔪.isClosedSubmanifold_N h𝔪.isSNCDivisor h𝔪.isTransverse
    h𝔪.isCoherent hne hmono 𝔪.d hyC.1).mpr ?_
  have hsum : ∑ i ∈ memberIdx 𝔪.E y, expDataAlong n 𝔪.N 𝔪.ideal 𝔪.E y i =
      ∑ i ∈ Finset.univ.filter (fun i => y ∈ 𝔪.E.get i), divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get i) y := by
    rw [memberIdx, Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.valEmbedding_apply, expDataAlong, dif_pos i.2, Fin.eta]
  rw [hsum]
  calc 𝔪.d ≤ ∑ j ∈ J, divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) x := hd
    _ = ∑ j ∈ J, divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) y :=
      Finset.sum_congr rfl fun j hj => (hy j hj hyC.1 (hyC.2 j hj)).symm
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => y ∈ 𝔪.E.get i), divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get i) y :=
      Finset.sum_le_sum_of_subset fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyC.2 j hj⟩

end Members

/-! ### One blowup along `N ∩ ⋂_J E_j` -/

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

open Classical in
/-- **`hir:monomial-blowup` at a point over the centre, for a centre admissible on the whole manifold.**  Let `𝔪` be well
formed, monomial and nonzero along `N` (`0 < n`), `J` a set of members, `C = N ∩ ⋂_{j ∈ J} E_j` an admissible centre, `π`
the blowup along `C`, and `z ∈ N'` over `x = π z ∈ C` with `∑_{j ∈ J} e_j(x) ≥ d`.  Then near `z` the transform is principal
monomial along `N'`: in centred coordinates at `z` adapted to `N'` and `E'`, `Res_{N'} 𝔞'_z` is generated by
`∏_{z ∈ E'_i} Θ_{σ i}^{a'_i}` with `a'_i = e_i(x)` on the strict transforms and `a'_D + d = ∑_{j ∈ J} e_j(x)` on the exceptional
member `D`; and the strict transform of some member of `J` misses `z`. -/
theorem monomial_blowup_of_isAdmissibleCentre (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (hmono : IsMonomialAlong n 𝔪.N 𝔪.ideal 𝔪.E)
    {J : Finset (Fin 𝔪.E.length)} (hC : 𝔪.IsAdmissibleCentre (𝔪.N ∩ memberInter 𝔪.E J)) {π : Y → X}
    (hπ : IsBlowupAlong n (𝔪.N ∩ memberInter 𝔪.E J) π) {z : Y}
    (hzN : z ∈ (𝔪.geoTransform (𝔪.N ∩ memberInter 𝔪.E J) π).N) (hz : π z ∈ 𝔪.N ∩ memberInter 𝔪.E J)
    (hd : 𝔪.d ≤ ∑ j ∈ J, divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) (π z)) :
    ∃ a' : Fin (𝔪.geoTransform (𝔪.N ∩ memberInter 𝔪.E J) π).E.length → ℕ,
      IsPrincipalAlongAt (𝔪.geoTransform (𝔪.N ∩ memberInter 𝔪.E J) π).N
        (𝔪.geoTransform (𝔪.N ∩ memberInter 𝔪.E J) π).ideal (𝔪.geoTransform (𝔪.N ∩ memberInter 𝔪.E J) π).E z a' ∧
      (∀ i (hi : i.1 < 𝔪.E.length), a' i = divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get ⟨i.1, hi⟩) (π z)) ∧
      (∀ i, ¬ i.1 < 𝔪.E.length → a' i + 𝔪.d = ∑ j ∈ J, divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) (π z)) ∧
      ∃ j ∈ J, z ∉ geoStrictTransform π (𝔪.N ∩ memberInter 𝔪.E J) (𝔪.E.get j) := by
  obtain ⟨k, Φ, σ, hΦsrc, -, hNflat, hσk, hσinj, hA, hgen⟩ :=
    isPrincipalAlongAt_of_isMonomialAlong hn h𝔪.isClosedSubmanifold_N h𝔪.isSNCDivisor h𝔪.isTransverse
      h𝔪.isCoherent hne hmono hz.1
  have hfilter := filter_eventually_subset_inter_memberInter_eq hn h𝔪.isSNCDivisor h𝔪.isTransverse hz.1 hz.2
  have hd' : 𝔪.d ≤ ∑ i ∈ Finset.univ.filter (fun i => π z ∈ 𝔪.E.get i ∧
      ∀ᶠ y in 𝓝 (π z), y ∈ 𝔪.N ∩ memberInter 𝔪.E J → y ∈ 𝔪.E.get i),
      divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get i) (π z) := by
    rw [hfilter]
    exact hd
  obtain ⟨k', Θ, σ', a', hΘt, hΘ0, hΘN, hσ'k, hσ'inj, hA', ha', hlast, hgen'⟩ :=
    MonomialBlowupAlongChart.exists_snc_chart_geoTransform_along_of_flat hπ h𝔪.isClosedSubmanifold_N
      h𝔪.isCoherent hC h𝔪.isSNCDivisor h𝔪.isTransverse hzN hz
      (T := Finset.univ.filter fun i => π z ∈ 𝔪.E.get i) (by simp)
      (fun i hi => hA i (Finset.mem_filter.mp hi).2) _ hgen hd'
  refine ⟨a', ⟨k', Θ, σ', hΘt, hΘ0, hΘN, hσ'k, hσ'inj, hA', hgen'⟩, ha', fun i hi => ?_, ?_⟩
  · rw [hlast i hi]
    rw [hfilter] at hd' ⊢
    omega
  · have hlt := BoundaryCountAlong.card_filter_mem_geoStrictTransform_lt_along hπ hC.subset_N h𝔪.isSNCDivisor
      h𝔪.isTransverse hC.2.2 J hz hzN (Eventually.of_forall fun y hyN hyJ => ⟨hyN, hyJ⟩)
    by_contra hall
    push Not at hall
    rw [Finset.filter_true_of_mem hall] at hlt
    exact lt_irrefl _ hlt

end Blowup

/-! ### `hir:monomial-blowup`: the local statement -/

section Local

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **The exponents of a restriction to an open set** are those of the marked ideal, member by member. -/
theorem divExpAlong_pullback_val_get (𝔪 : MarkedIdeal n X) (h𝔞 : 𝔪.ideal.IsCoherent) (U : Opens X) (p : U) {i : ℕ}
    (hi : i < (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).E.length) (hi' : i < 𝔪.E.length) :
    divExpAlong n (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).N (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).ideal
        ((MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).E.get ⟨i, hi⟩) p =
      divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get ⟨i, hi'⟩) p.1 := by
  have hget : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).E.get ⟨i, hi⟩ =
      (Subtype.val : U → X) ⁻¹' 𝔪.E.get ⟨i, hi'⟩ := by
    simp [MarkedIdeal.pullback]
  rw [hget]
  refine MonomialInvariantFunctorialAlong.divExpAlong_pullback (φ := (Subtype.val : U → X)) (fun e => ?_) ?_ _
  · exact MarkedIdealRestrictOpen.cosupp_pullback_val (⟨𝔪.N, [], 𝔪.ideal, e⟩ : MarkedIdeal n X)
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) U
  · exact map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (U : Set X)) p.2 (U.isOpen.mem_nhds p.2)

open Classical in
/-- **Monomial marked ideals under the blowup of an intersection of members** (`hir:monomial-blowup`).  Let `𝔪` be well
formed, monomial and nonzero along `N` (`0 < n`), `x ∈ N`, `J` a set of members through `x` with `∑_{j ∈ J} a_j ≥ d`
(`a_j = e_j(x)` the exponents along `N`), and `C = N ∩ ⋂_{j ∈ J} E_j`.  Then there is an open neighbourhood `U` of `x` on which
`C` is an admissible centre of `𝔪|_U`, and for every blowup `π` of `U` along `C ∩ U` and every point `z` of the strict
transform `N'` over `x`: the transform is principal monomial along `N'` at `z`, generated on `N'` by
`∏_{z ∈ E'_i} Θ_{σ i}^{a'_i}` in coordinates at `z` adapted to `N'` and `E'`, with `a'_i = a_i` on the strict transforms
of the members and `a'_D = ∑_{j ∈ J} a_j - d` on the exceptional member `D = π⁻¹(C)`; and the strict transform of some
member of `J` does not pass through `z` (`S(z)` does not contain `J`). -/
theorem monomial_blowup (hn : 0 < n) {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (hmono : IsMonomialAlong n 𝔪.N 𝔪.ideal 𝔪.E)
    {J : Finset (Fin 𝔪.E.length)} {x : X} (hxN : x ∈ 𝔪.N) (hxJ : ∀ j ∈ J, x ∈ 𝔪.E.get j)
    (hd : 𝔪.d ≤ ∑ j ∈ J, divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) x) :
    ∃ U : Opens X, x ∈ U ∧
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).IsAdmissibleCentre
        ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J)) ∧
      ∀ {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {π : Y → U},
        IsBlowupAlong n ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J)) π → ∀ z : Y,
        z ∈ ((MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).geoTransform
          ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J)) π).N → (π z : X) = x →
        ∃ a' : Fin ((MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).geoTransform
            ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J)) π).E.length → ℕ,
          IsPrincipalAlongAt ((MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).geoTransform
              ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J)) π).N
            ((MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).geoTransform
              ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J)) π).ideal
            ((MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).geoTransform
              ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J)) π).E z a' ∧
          (∀ i (hi : i.1 < 𝔪.E.length), a' i = divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get ⟨i.1, hi⟩) x) ∧
          (∀ i, ¬ i.1 < 𝔪.E.length → a' i + 𝔪.d = ∑ j ∈ J, divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) x) ∧
          ∃ j ∈ J, z ∉ geoStrictTransform π ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J))
            ((Subtype.val : U → X) ⁻¹' 𝔪.E.get j) := by
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.mp (eventually_mem_cosupp_of_le_sum hn h𝔪 hne hmono hxN hxJ hd)
  set U : Opens X := ⟨t, hto⟩ with hUdef
  set 𝔪U := MarkedIdeal.pullback (Subtype.val : U → X) 𝔪 with h𝔪U
  have hlen : 𝔪.E.length = 𝔪U.E.length := by simp [h𝔪U, MarkedIdeal.pullback]
  set e : Fin 𝔪.E.length ↪ Fin 𝔪U.E.length := (finCongr hlen).toEmbedding with hedef
  have hget : ∀ j : Fin 𝔪.E.length, 𝔪U.E.get (e j) = (Subtype.val : U → X) ⁻¹' 𝔪.E.get j := by
    intro j
    simp [h𝔪U, hedef, MarkedIdeal.pullback]
  set J' := J.map e with hJ'
  have hmemJ' : memberInter 𝔪U.E J' = (Subtype.val : U → X) ⁻¹' memberInter 𝔪.E J := by
    ext p
    simp only [memberInter, Set.mem_ofPred_eq, mem_preimage, hJ', Finset.mem_map]
    constructor
    · intro h j hj
      have := h (e j) ⟨j, hj, rfl⟩
      rwa [hget] at this
    · rintro h _ ⟨j, hj, rfl⟩
      rw [hget]
      exact h j hj
  have hCeq : (Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J) = 𝔪U.N ∩ memberInter 𝔪U.E J' := by
    rw [hmemJ']
    rfl
  have hwfU : 𝔪U.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val h𝔪 U
  have hneU := MonomialCaseLocal.isNonzeroAlongAt_pullback_val h𝔪.isCoherent hne U
  have hmonoU := MonomialCaseLocal.isMonomialAlong_pullback_val_of_isMonomialAlong h𝔪.isCoherent hmono U
  have hCU : 𝔪U.IsAdmissibleCentre (𝔪U.N ∩ memberInter 𝔪U.E J') := by
    refine MemberInterAlong.isAdmissibleCentre_inter_memberInter_of_isWellFormed hn hwfU J' ?_
    rw [← hCeq, h𝔪U, MarkedIdealRestrictOpen.cosupp_pullback_val 𝔪
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔪.isCoherent hg) U]
    intro p hp
    exact ht p.1 p.2 hp
  have hexp : ∀ (p : U) (j : Fin 𝔪.E.length),
      divExpAlong n 𝔪U.N 𝔪U.ideal (𝔪U.E.get (e j)) p = divExpAlong n 𝔪.N 𝔪.ideal (𝔪.E.get j) p.1 := by
    intro p j
    exact divExpAlong_pullback_val_get 𝔪 h𝔪.isCoherent U p (e j).2 j.2
  refine ⟨U, hxt, by rw [hCeq]; exact hCU, ?_⟩
  intro Y _ _ _ π hπ z hzN hzx
  have hzC : π z ∈ (Subtype.val : U → X) ⁻¹' (𝔪.N ∩ memberInter 𝔪.E J) := by
    show (π z : X) ∈ 𝔪.N ∩ memberInter 𝔪.E J
    rw [hzx]
    exact ⟨hxN, hxJ⟩
  have hdU : 𝔪U.d ≤ ∑ j ∈ J', divExpAlong n 𝔪U.N 𝔪U.ideal (𝔪U.E.get j) (π z) := by
    rw [hJ', Finset.sum_map]
    simp only [hexp, hzx]
    exact hd
  rw [hCeq] at hπ hzN hzC ⊢
  obtain ⟨a', hP, ha', hlast, j, hj, hjz⟩ :=
    monomial_blowup_of_isAdmissibleCentre hn hwfU hneU hmonoU hCU hπ hzN hzC hdU
  refine ⟨a', hP, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · have hiU : i.1 < 𝔪U.E.length := hlen ▸ hi
    rw [ha' i hiU, divExpAlong_pullback_val_get 𝔪 h𝔪.isCoherent U (π z) hiU hi, hzx]
  · have hiU : ¬ i.1 < 𝔪U.E.length := hlen ▸ hi
    refine (hlast i hiU).trans ?_
    rw [hJ', Finset.sum_map]
    simp only [hexp, hzx]
  · obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_map.mp (hJ' ▸ hj)
    refine ⟨j₀, hj₀, ?_⟩
    rw [← hget]
    exact hjz

end Local

end

end Hironaka.HironakaMonomialBlowup
