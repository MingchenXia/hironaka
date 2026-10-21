import TranscendentalNakamaye.Pending.DerivativeIdealTower
import TranscendentalNakamaye.Pending.HomogenizedGlueing
import TranscendentalNakamaye.Pending.MarkedIdealOperationsTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Sums of finitely many marked ideals and the coefficient ideal

Hironaka phase H3 (TN23-ENVELOPES, agreed with TN-CLASSICAL on I-0981); blueprint
`mc:finite-sum`, `mc:marked-finite-sum`, `mc:marked-finite-sum-tower`, `mc:coefficient-ideal`,
`mc:coefficient-equivalent` (`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005, §2.9
(the sum `(𝓘₁, μ₁) + … + (𝓘ₘ, μₘ) = (∑ᵢ 𝓘ᵢ^{∏_{j≠i} μⱼ}, ∏ⱼ μⱼ)`, Lemma `le:operations` (1)) and §2.11
(the coefficient ideal `𝓒(𝓘, μ) = (𝓘, μ) + (𝓓𝓘, μ - 1) + … + (𝓓^{μ-1}𝓘, 1)` and Lemma `le:coeff`
`𝓒(𝓘, μ) ≃ (𝓘, μ)`), for `N = M` and TN-CLASSICAL's transform with centre-relative strict transforms
(`geoTransformAlong`, `IsGeoTestTower`); the binary case is TN-CLASSICAL's
`MarkedIdealOperationsTransform.MarkedIdeal.geoTransformAlong_add`.

* `finSumIdeal_one`, `finSumIdeal_congr`, `finSumIdeal_le`, `isCoherent_finSumIdeal_of_lt`,
  `mem_cosupport_finSumIdeal` (`cosupp(∑ᵢ 𝔍ᵢ, μ) = ⋂ᵢ cosupp(𝔍ᵢ, μ)`), `controlledTransform_finSumIdeal`
  (`σ^c(∑ᵢ 𝔍ᵢ, μ) = ∑ᵢ σ^c(𝔍ᵢ, μ)` for `𝔍ᵢ ⊆ 𝓘_C^μ`).
* `msum 𝔪 m`: Włodarczyk's sum of `𝔪 0, …, 𝔪 (m - 1)`; `IsAmbientFamily` (`N = M`, common `E`,
  coherent ideals, marks `≥ 1`); `cosupp_msum`, `isAdmissibleCentre_msum_iff`, `geoTransform_msum`;
  `geoTransformAlong_msum` (**`le:operations` (1)** for `m` summands: the multiple test blow-ups of the
  sum are the simultaneous ones of the summands, and the transform of the sum is the sum of the
  transforms).
* `coeffMarked 𝔪 = msum (𝓓^i 𝔪)_{i<d}` and `coeff_tower` (**`le:coeff`**): for `N = M`, `𝔞` coherent,
  `d ≥ 1`, the multiple test blow-ups of `𝓒(𝔪)` and of `𝔪` coincide, and along them
  `cosupp 𝓒(𝔪)_T = cosupp 𝔪_T`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace TranscendentalNakamaye.Pending.CoefficientIdeal

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers BlowupControlledTransform BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueing DerivativeIdealTower RestrictedIdealExtension

noncomputable section

/-! ### Finite sums of ideals -/

section FinSum

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `finSumIdeal J 1 = J 0` for a coherent `J 0`. -/
theorem finSumIdeal_one {J : ℕ → GermIdeal n M} (hJ : (J 0).IsCoherent) : finSumIdeal J 1 = J 0 := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine HomogenizedIdeal.mem_of_isInSpanAt hJ (IsInSpanAt.mono ?_
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < 1 ∧ (J i).mem y s) y g from hg))
    rintro s ⟨i, hi, hs⟩
    obtain rfl : i = 0 := by omega
    exact hs
  · show IsInSpanAt (n := n) (fun s => ∃ i, i < 1 ∧ (J i).mem y s) y g
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨0, Nat.one_pos, hg⟩ (holomorphicAt_of_mem hJ hg)

/-- Only the members `J i`, `i < m`, matter. -/
theorem finSumIdeal_congr {J J' : ℕ → GermIdeal n M} {m : ℕ} (h : ∀ i < m, J i = J' i) :
    finSumIdeal J m = finSumIdeal J' m := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J' i).mem y s) y g
    exact IsInSpanAt.mono (fun s ⟨i, hi, hs⟩ => ⟨i, hi, h i hi ▸ hs⟩)
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem y s) y g from hg)
  · show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem y s) y g
    exact IsInSpanAt.mono (fun s ⟨i, hi, hs⟩ => ⟨i, hi, (h i hi).symm ▸ hs⟩)
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J' i).mem y s) y g from hg)

/-- A finite sum of ideals contained in a coherent ideal `𝔅` is contained in `𝔅`. -/
theorem finSumIdeal_le {J : ℕ → GermIdeal n M} {m : ℕ} {𝔅 : GermIdeal n M} (h𝔅 : 𝔅.IsCoherent)
    (h : ∀ i < m, (J i).Le 𝔅) : (finSumIdeal J m).Le 𝔅 := fun y g hg =>
  HomogenizedIdeal.mem_of_isInSpanAt h𝔅 (IsInSpanAt.mono (fun s ⟨i, hi, hs⟩ => h i hi y s hs)
    (show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem y s) y g from hg))

/-- **A finite sum of coherent ideals is coherent** (only the members `i < m` are assumed coherent). -/
theorem isCoherent_finSumIdeal_of_lt {J : ℕ → GermIdeal n M} :
    ∀ {m : ℕ}, (∀ i < m, (J i).IsCoherent) → (finSumIdeal J m).IsCoherent
  | 0, _ => by
    rw [finSumIdeal_congr (J' := fun _ => unitIdeal n M) (fun i hi => absurd hi (Nat.not_lt_zero i))]
    exact isCoherent_finSumIdeal (fun _ => isCoherent_unitIdeal) 0
  | m + 1, hJ => by
    rw [finSumIdeal_succ fun i hi => hJ i (Nat.lt_succ_of_le hi)]
    exact isCoherent_sumIdeal (isCoherent_finSumIdeal_of_lt fun i hi => hJ i (Nat.lt_succ_of_lt hi))
      (hJ m (Nat.lt_succ_self m))

/-- **The cosupport of a finite sum** (equal marks): `cosupp(∑_{i<m} 𝔍ᵢ, μ) = ⋂_{i<m} cosupp(𝔍ᵢ, μ)`. -/
theorem mem_cosupport_finSumIdeal {N : Set M} {J : ℕ → GermIdeal n M} {m μ : ℕ}
    (hJ : ∀ i < m, ∀ x g, (J i).mem x g → HolomorphicAt n g x) {x : M} :
    x ∈ cosupport n N (finSumIdeal J m) μ ↔ x ∈ N ∧ ∀ i < m, x ∈ cosupport n N (J i) μ := by
  constructor
  · rintro ⟨hxN, hx⟩
    refine ⟨hxN, fun i hi => ⟨hxN, fun g hg => hx g ?_⟩⟩
    exact (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ i, i < m ∧ (J i).mem x s)
      ⟨i, hi, hg⟩ (hJ i hi x g hg) : IsInSpanAt (n := n) _ x g)
  · rintro ⟨hxN, hx⟩
    refine ⟨hxN, fun g hg => IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn
      (show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem x s) x g from hg) ?_⟩
    rintro s ⟨i, hi, hs⟩
    exact (hx i hi).2 s hs

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {C : Set M} {π : M' → M}

/-- **Controlled transforms of finite sums** (equal marks, `m ≥ 1`): for coherent `𝔍ᵢ ⊆ 𝓘_C^μ`,
`σ^c(∑_{i<m} 𝔍ᵢ, μ) = ∑_{i<m} σ^c(𝔍ᵢ, μ)`. -/
theorem controlledTransform_finSumIdeal (hπ : IsBlowupAlong n C π) {J : ℕ → GermIdeal n M} {μ : ℕ} :
    ∀ {m : ℕ}, 1 ≤ m → (∀ i < m, (J i).IsCoherent) →
      (∀ i < m, (J i).Le (idealPow (vanishingIdeal (n := n) C) μ)) →
      controlledTransform hπ (finSumIdeal J m) μ =
        finSumIdeal (fun i => controlledTransform hπ (J i) μ) m
  | 0, h, _, _ => absurd h (by omega)
  | 1, _, hJ, hle => by
    rw [finSumIdeal_one (hJ 0 Nat.one_pos),
      finSumIdeal_one (J := fun i => controlledTransform hπ (J i) μ)
        (isCoherent_controlledTransform hπ (hJ 0 Nat.one_pos) (hle 0 Nat.one_pos))]
  | m + 2, _, hJ, hle => by
    have hJ' : ∀ i < m + 1, (J i).IsCoherent := fun i hi => hJ i (by omega)
    have hle' : ∀ i < m + 1, (J i).Le (idealPow (vanishingIdeal (n := n) C) μ) :=
      fun i hi => hle i (by omega)
    have hB := GermIdealPullbackCalculus.isCoherent_idealPow
      (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ) μ
    rw [finSumIdeal_succ fun i hi => hJ i (by omega),
      MarkedIdealOperationsTransform.controlledTransform_sumIdeal hπ (isCoherent_finSumIdeal_of_lt hJ')
        (hJ (m + 1) (by omega)) (finSumIdeal_le hB hle') (hle (m + 1) (by omega)),
      controlledTransform_finSumIdeal hπ (by omega) hJ' hle']
    exact (finSumIdeal_succ (J := fun i => controlledTransform hπ (J i) μ) (μ := m + 1) fun i hi =>
      isCoherent_controlledTransform hπ (hJ i (by omega)) (hle i (by omega))).symm

end FinSum

/-! ### Włodarczyk's sum of finitely many marked ideals -/

section MSum

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The exponent of the `i`-th summand: `∏_{j < m, j ≠ i} dⱼ`. -/
def sumExp (d : ℕ → ℕ) (m i : ℕ) : ℕ := ((Finset.range m).erase i).prod d

theorem mul_sumExp (d : ℕ → ℕ) {m i : ℕ} (hi : i < m) :
    d i * sumExp d m i = (Finset.range m).prod d := by
  rw [sumExp, Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hi)]

theorem one_le_sumExp {d : ℕ → ℕ} {m : ℕ} (hd : ∀ j < m, 1 ≤ d j) (i : ℕ) : 1 ≤ sumExp d m i := by
  have h : 0 < ((Finset.range m).erase i).prod d := Finset.prod_pos fun j hj => by
    have := hd j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
    omega
  unfold sumExp
  omega

/-- **Włodarczyk's sum of marked ideals** (§2.9):
`(𝓘₀, μ₀) + … + (𝓘_{m-1}, μ_{m-1}) = (∑ᵢ 𝓘ᵢ^{∏_{j≠i} μⱼ}, ∏ⱼ μⱼ)`, on the `N` and `E` of `𝔪 0`. -/
def msum (𝔪 : ℕ → MarkedIdeal n M) (m : ℕ) : MarkedIdeal n M where
  N := (𝔪 0).N
  E := (𝔪 0).E
  ideal := finSumIdeal (fun i => idealPow (𝔪 i).ideal (sumExp (fun j => (𝔪 j).d) m i)) m
  d := (Finset.range m).prod fun j => (𝔪 j).d

variable [IsComplexManifold n M]

/-- A family of marked ideals on `N = M` with a common `E`, coherent ideals and marks `≥ 1`. -/
structure IsAmbientFamily (𝔪 : ℕ → MarkedIdeal n M) (m : ℕ) : Prop where
  N : ∀ i < m, (𝔪 i).N = univ
  E : ∀ i < m, (𝔪 i).E = (𝔪 0).E
  coh : ∀ i < m, (𝔪 i).ideal.IsCoherent
  d : ∀ i < m, 1 ≤ (𝔪 i).d

variable {𝔪 : ℕ → MarkedIdeal n M} {m : ℕ}

theorem IsAmbientFamily.isCoherent_msum (h : IsAmbientFamily 𝔪 m) : (msum 𝔪 m).ideal.IsCoherent :=
  isCoherent_finSumIdeal_of_lt fun i hi => GermIdealPullbackCalculus.isCoherent_idealPow (h.coh i hi) _

/-- **The cosupport of a sum** is the intersection of the cosupports (`N = M`, marks `≥ 1`). -/
theorem cosupp_msum (h : IsAmbientFamily 𝔪 m) (hm : 1 ≤ m) :
    (msum 𝔪 m).cosupp = {x | ∀ i < m, x ∈ (𝔪 i).cosupp} := by
  ext x
  have hhol : ∀ i < m, ∀ y g,
      (idealPow (𝔪 i).ideal (sumExp (fun j => (𝔪 j).d) m i)).mem y g → HolomorphicAt n g y :=
    fun i _ y g hg => holomorphicAt_of_mem_idealPow hg
  show x ∈ cosupport n (𝔪 0).N
    (finSumIdeal (fun i => idealPow (𝔪 i).ideal (sumExp (fun j => (𝔪 j).d) m i)) m)
    ((Finset.range m).prod fun j => (𝔪 j).d) ↔ _
  rw [h.N 0 hm, mem_cosupport_finSumIdeal hhol]
  simp only [mem_univ, true_and, Set.mem_ofPred_eq]
  refine forall₂_congr fun i hi => ?_
  have hpow := OrderMultiplicativity.cosupport_idealPow_mul_eq
    (fun y g hg => holomorphicAt_of_mem (h.coh i hi) hg)
    (one_le_sumExp h.d i) (𝔪 i).d
  rw [mul_sumExp (fun j => (𝔪 j).d) hi] at hpow
  rw [hpow, MarkedIdeal.cosupp, h.N i hi]

/-- **A centre is admissible for a sum iff it is admissible for every summand.** -/
theorem isAdmissibleCentre_msum_iff (h : IsAmbientFamily 𝔪 m) (hm : 1 ≤ m) {C : Set M} :
    (msum 𝔪 m).IsAdmissibleCentre C ↔ ∀ i < m, (𝔪 i).IsAdmissibleCentre C := by
  rw [IsAdmissibleCentre, cosupp_msum h hm]
  constructor
  · rintro ⟨hC, hsub, hnc⟩ i hi
    exact ⟨hC, fun x hx => hsub hx i hi, by rw [h.E i hi]; exact hnc⟩
  · intro hall
    exact ⟨(hall 0 hm).1, fun x hx i hi => (hall i hi).2.1 hx, (hall 0 hm).2.2⟩

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {C : Set M} {π : M' → M}

/-- **One step of `le:operations` (1)**: the transform of a sum is the sum of the transforms. -/
theorem geoTransform_msum (h : IsAmbientFamily 𝔪 m) (hm : 1 ≤ m) (hπ : IsBlowupAlong n C π)
    (hC : ∀ i < m, (𝔪 i).IsAdmissibleCentre C) :
    (msum 𝔪 m).geoTransform C π = msum (fun i => (𝔪 i).geoTransform C π) m := by
  have hle : ∀ i < m, (𝔪 i).ideal.Le (idealPow (vanishingIdeal (n := n) C) (𝔪 i).d) := fun i hi =>
    HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre (h.N i hi) (h.coh i hi) (hC i hi)
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have hlepow : ∀ i < m, (idealPow (𝔪 i).ideal (sumExp (fun j => (𝔪 j).d) m i)).Le
      (idealPow (vanishingIdeal (n := n) C) ((Finset.range m).prod fun j => (𝔪 j).d)) :=
      fun i hi => by
    have := MarkedIdealOperationsTransform.idealPow_mono (hle i hi) (sumExp (fun j => (𝔪 j).d) m i)
    rwa [MarkedIdealOperationsTransform.idealPow_idealPow hIC, mul_sumExp (fun j => (𝔪 j).d) hi]
      at this
  have hideal : ((msum 𝔪 m).geoTransform C π).ideal =
      (msum (fun i => (𝔪 i).geoTransform C π) m).ideal := by
    have hN : (msum 𝔪 m).N = univ := h.N 0 hm
    rw [geoTransform_ideal_eq_controlledTransform hN h.isCoherent_msum hπ]
    show controlledTransform hπ (finSumIdeal (fun i => idealPow (𝔪 i).ideal
        (sumExp (fun j => (𝔪 j).d) m i)) m) ((Finset.range m).prod fun j => (𝔪 j).d) = _
    rw [controlledTransform_finSumIdeal hπ hm
      (fun i hi => GermIdealPullbackCalculus.isCoherent_idealPow (h.coh i hi) _) hlepow]
    refine finSumIdeal_congr fun i hi => ?_
    rw [geoTransform_ideal_eq_controlledTransform (h.N i hi) (h.coh i hi) hπ,
      ← MarkedIdealOperationsTransform.controlledTransform_idealPow hπ (h.coh i hi) (hle i hi),
      ← mul_sumExp (fun j => (𝔪 j).d) hi]
    rfl
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hideal rfl

/-- One admissible step keeps an ambient family ambient. -/
theorem IsAmbientFamily.geoTransform (h : IsAmbientFamily 𝔪 m) (hπ : IsBlowupAlong n C π)
    (hC : ∀ i < m, (𝔪 i).IsAdmissibleCentre C) :
    IsAmbientFamily (fun i => (𝔪 i).geoTransform C π) m where
  N i hi := geoTransform_N_eq_univ (h.N i hi) hπ
  E i hi := by simp only [geoTransform_E, h.E i hi]
  coh i hi := by
    rw [geoTransform_ideal_eq_controlledTransform (h.N i hi) (h.coh i hi) hπ]
    exact isCoherent_controlledTransform hπ (h.coh i hi)
      (HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre (h.N i hi) (h.coh i hi) (hC i hi))
  d i hi := h.d i hi

end MSum

/-! ### Along towers -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Włodarczyk `le:operations` (1)** for `m ≥ 1` summands (`N = M`, common `E`, coherent ideals,
marks `≥ 1`): the multiple test blow-ups of `𝔪 0 + … + 𝔪 (m - 1)` are exactly the simultaneous
multiple test blow-ups of the `𝔪 i`, and along them the transform of the sum is the sum of the
transforms. -/
theorem geoTransformAlong_msum (𝔪 : ℕ → MarkedIdeal n X) {m : ℕ} (hm : 1 ≤ m)
    (h : IsAmbientFamily 𝔪 m) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (IsGeoTestTower (msum 𝔪 m) T ↔ ∀ i < m, IsGeoTestTower (𝔪 i) T) ∧
      ((∀ i < m, IsGeoTestTower (𝔪 i) T) →
        geoTransformAlong (msum 𝔪 m) T = msum (fun i => geoTransformAlong (𝔪 i) T) m ∧
        IsAmbientFamily (fun i => geoTransformAlong (𝔪 i) T) m)
  | _, .refl => ⟨by simp [IsGeoTestTower], fun _ => ⟨rfl, h⟩⟩
  | _, .step T C π hπ => by
      obtain ⟨ihT, ihE⟩ := geoTransformAlong_msum 𝔪 hm h T
      refine ⟨?_, fun hall => ?_⟩
      · simp only [isGeoTestTower_step_iff]
        constructor
        · rintro ⟨hT, hC⟩
          have hTi := ihT.mp hT
          obtain ⟨heq, hfam⟩ := ihE hTi
          rw [heq, isAdmissibleCentre_msum_iff hfam hm] at hC
          exact fun i hi => ⟨hTi i hi, hC i hi⟩
        · intro hall
          have hTi : ∀ i < m, IsGeoTestTower (𝔪 i) T := fun i hi => (hall i hi).1
          obtain ⟨heq, hfam⟩ := ihE hTi
          refine ⟨ihT.mpr hTi, ?_⟩
          rw [heq, isAdmissibleCentre_msum_iff hfam hm]
          exact fun i hi => (hall i hi).2
      · have hTi : ∀ i < m, IsGeoTestTower (𝔪 i) T := fun i hi =>
          ((isGeoTestTower_step_iff (𝔪 i) T C π hπ).mp (hall i hi)).1
        have hCi : ∀ i < m, (geoTransformAlong (𝔪 i) T).IsAdmissibleCentre C := fun i hi =>
          ((isGeoTestTower_step_iff (𝔪 i) T C π hπ).mp (hall i hi)).2
        obtain ⟨heq, hfam⟩ := ihE hTi
        refine ⟨?_, hfam.geoTransform hπ hCi⟩
        rw [geoTransformAlong_step, heq, geoTransform_msum hfam hm hπ hCi]
        rfl

/-! ### The coefficient ideal -/

/-- `𝓓^0(𝔪) = 𝔪`. -/
theorem derivMarked_zero {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    (𝔪 : MarkedIdeal n M) : derivMarked 𝔪 0 = 𝔪 := by
  cases 𝔪; rfl

/-- **The coefficient ideal** (Włodarczyk §2.11): `𝓒(𝔪) = 𝔪 + 𝓓(𝔪) + … + 𝓓^{d-1}(𝔪)`, i.e.
`(𝓘, μ) + (𝓓𝓘, μ - 1) + … + (𝓓^{μ-1}𝓘, 1)` for `𝔪 = (M, N, E, 𝓘, μ)`. -/
def coeffMarked {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    (𝔪 : MarkedIdeal n M) : MarkedIdeal n M :=
  msum (fun i => derivMarked 𝔪 i) 𝔪.d

/-- The derivatives `𝓓^i(𝔪)`, `i < d`, form an ambient family. -/
theorem isAmbientFamily_derivMarked {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {𝔪 : MarkedIdeal n M}
    (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) :
    IsAmbientFamily (fun i => derivMarked 𝔪 i) 𝔪.d where
  N _ _ := hN
  E _ _ := rfl
  coh i _ := isCoherent_iterDerivIdeal h𝔞 i
  d i hi := by simp only [derivMarked_d]; omega

/-- **Włodarczyk, Lemma `le:coeff`: `𝓒(𝔪) ≃ 𝔪`** (`N = M`, `𝔞` coherent, `d ≥ 1`): a tower is a
multiple test blow-up of `𝓒(𝔪)` iff it is one of `𝔪`, and along it the cosupports of the transforms
agree. -/
theorem coeff_tower (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (IsGeoTestTower (coeffMarked 𝔪) T ↔ IsGeoTestTower 𝔪 T) ∧
      (IsGeoTestTower 𝔪 T →
        (geoTransformAlong (coeffMarked 𝔪) T).cosupp = (geoTransformAlong 𝔪 T).cosupp) := by
  have hfam := isAmbientFamily_derivMarked hN h𝔞
  obtain ⟨hiff, heq⟩ := geoTransformAlong_msum (fun i => derivMarked 𝔪 i) hd hfam T
  have hall : IsGeoTestTower 𝔪 T → ∀ i < 𝔪.d, IsGeoTestTower (derivMarked 𝔪 i) T :=
    fun hT i hi => (inclusions_tower 𝔪 hN h𝔞 (le_of_lt hi) T hT).1
  refine ⟨⟨fun hC => ?_, fun hT => (show IsGeoTestTower (msum _ _) T from hiff.mpr (hall hT))⟩,
    fun hT => ?_⟩
  · have := hiff.mp hC 0 hd
    rwa [derivMarked_zero] at this
  · obtain ⟨he, hfamT⟩ := heq (hall hT)
    rw [show coeffMarked 𝔪 = msum (fun i => derivMarked 𝔪 i) 𝔪.d from rfl, he,
      cosupp_msum hfamT hd]
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx
      have := hx 0 hd
      rwa [derivMarked_zero] at this
    · intro hx i hi
      obtain ⟨-, hNT, hNDT, -, -, -, hle⟩ := inclusions_tower 𝔪 hN h𝔞 (le_of_lt hi) T hT
      have hdT : i ≤ (geoTransformAlong 𝔪 T).d := by
        rw [d_geoTransformAlong]; exact le_of_lt hi
      have h1 := cosupp_subset_cosupp_derivMarked hNT hdT hx
      show x ∈ cosupport n (geoTransformAlong (derivMarked 𝔪 i) T).N
        (geoTransformAlong (derivMarked 𝔪 i) T).ideal (geoTransformAlong (derivMarked 𝔪 i) T).d
      rw [hNDT, d_geoTransformAlong, derivMarked_d]
      have h1' : x ∈ cosupport n univ (iterDerivIdeal (geoTransformAlong 𝔪 T).ideal i)
          ((geoTransformAlong 𝔪 T).d - i) := by
        have := h1
        rwa [MarkedIdeal.cosupp, derivMarked_N, hNT] at this
      rw [d_geoTransformAlong] at h1'
      exact cosupport_subset_of_le hle _ h1'

end Tower

end

end TranscendentalNakamaye.Pending.CoefficientIdeal
