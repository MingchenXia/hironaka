import Hironaka.Analytic.Unibranch.HironakaG10GnIrreducible
import Hironaka.Analytic.Unibranch.HironakaG10TmLocalFlatness

/-!
# Generic flatness at a fixed fibre point: the hypothesis `hGF` of route G is a theorem

Lane G10GN, run 0081 (`work/hironaka-run0081-20261117/G10GN/hGF-route.md`, item G10GN-N5). Frisch, *Points de
platitude d'un morphisme d'espaces analytiques complexes*, Invent. Math. 4 (1967), Th. (II,1) (i)+(ii) and the local
criterion of flatness: for a relatively exact start `(G, A)` over a parameter set `P ⊆ ℂᵐ` analytic near `p₀ ∈ P`,
the parameters `p ∈ P` near `p₀` at which the fibre start is not exact at `y₀` lie in an analytic subset `P''` of
`P`, nowhere dense in `P`.

**`hGF_holds`** states exactly the hypothesis `hGF` of `HironakaG10RmRelStart.isConstructibleNear_fibreExact_of_hGF`
(and of `HironakaG10FrRouteG.isConstructibleNear_fibreExact` for `W = ℂᵗ`).

Proof: decompose the germ of `P` at `p₀` into irreducible germs `P₁, …, P_r`
(`AnalyticGermDecomposition.exists_irreducible_decomposition_euclidean`); on each `Pᵢ` generic chart flatness off
`{gᵢ = 0}` (`HironakaG10GnIrreducible.exists_flat_irreducible`); `P'' = ⋃ᵢ (Pᵢ ∩ {gᵢ = 0}) ∪ ⋃_{i ≠ j} (Pᵢ ∩ Pⱼ)`
is nowhere dense (proper analytic subgerms of irreducible germs are thin, `IrreducibleGermLocal.exists_thin_nhds`);
off `P''` the germ of `P` is that of one `Pᵢ`, and flatness gives fibre exactness (lane G10LF's local criterion
`HironakaG10TmLocalFlatness.chartFlat_iff_fibreExactAt` with the start modulo `I_P` of
`HironakaG10GfModStart.exactStartMod_of_relExactStartOn`).

No named input. BP: hironaka-g10gn-hgf.tex.
-/

set_option autoImplicit false

open Set Filter Function
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GnHGF

noncomputable section

open Hironaka Hironaka
open HolGerm OkaRelationSheaf OkaGermBridge AnalyticGermDecomposition HironakaG10LocRelative
  HironakaG10LocFibreOpen Hironaka.Analytic.Unibranch.HironakaG10GfModStart Hironaka.Analytic.Unibranch.HironakaG10FrRouteG
  Hironaka.Analytic.Unibranch.HironakaG10GnIrreducible

variable {m : ℕ}

/-! ### Thin subsets -/

/-- `T` is thin in `Q` on `N`: every open `O ⊆ N` meeting `Q` meets `Q ∖ T`. -/
def ThinIn (N Q T : Set (ComplexModel m)) : Prop :=
  ∀ O : Set (ComplexModel m), IsOpen O → O ⊆ N → (O ∩ Q).Nonempty → ∃ y ∈ O ∩ Q, y ∉ T

theorem ThinIn.mono {N N' Q T : Set (ComplexModel m)} (h : ThinIn N Q T) (hN : N' ⊆ N) : ThinIn N' Q T :=
  fun O hO hON hne => h O hO (hON.trans hN) hne

theorem ThinIn.union {N Q T T' : Set (ComplexModel m)} (h : ThinIn N Q T) (h' : ThinIn N Q T')
    (hT : IsHolZeroSetOn N T) : ThinIn N Q (T ∪ T') := by
  intro O hO hON hne
  obtain ⟨y₁, ⟨hy₁O, hy₁Q⟩, hy₁T⟩ := h O hO hON hne
  obtain ⟨y, ⟨⟨hyO, hyT⟩, hyQ⟩, hyT'⟩ := h' (O \ T) (hT.isOpen_sdiff hO hON)
    (sdiff_subset.trans hON) ⟨y₁, ⟨hy₁O, hy₁T⟩, hy₁Q⟩
  exact ⟨y, ⟨hyO, hyQ⟩, fun h => h.elim hyT hyT'⟩

theorem thinIn_empty (N Q : Set (ComplexModel m)) : ThinIn N Q ∅ :=
  fun _ _ _ ⟨y, hy⟩ => ⟨y, hy, Set.notMem_empty y⟩

theorem isHolZeroSetOn_empty (N : Set (ComplexModel m)) : IsHolZeroSetOn N ∅ :=
  ⟨1, fun _ _ => 1, fun _ => differentiableOn_const 1, by ext p; simp⟩

theorem isHolZeroSetOn_inter {N A B : Set (ComplexModel m)} (hA : IsHolZeroSetOn N A)
    (hB : IsHolZeroSetOn N B) : IsHolZeroSetOn N (A ∩ B) := by
  obtain ⟨r, g, hg, hgA⟩ := hA
  obtain ⟨s, h, hh, hhB⟩ := hB
  refine ⟨r + s, fun k => Sum.elim g h (finSumFinEquiv.symm k), fun k => ?_, ?_⟩
  · show DifferentiableOn ℂ (Sum.elim g h (finSumFinEquiv.symm k)) N
    generalize finSumFinEquiv.symm k = x
    cases x with
    | inl i => exact hg i
    | inr j => exact hh j
  · ext p
    have h1 := Set.ext_iff.mp hgA p
    have h2 := Set.ext_iff.mp hhB p
    simp only [mem_inter_iff, mem_ofPred_eq] at h1 h2 ⊢
    constructor
    · rintro ⟨⟨hpA, hpB⟩, hpN⟩
      refine ⟨hpN, fun k => ?_⟩
      rcases finSumFinEquiv.symm k with i | j
      · exact (h1.mp ⟨hpA, hpN⟩).2 i
      · exact (h2.mp ⟨hpB, hpN⟩).2 j
    · rintro ⟨hpN, hk⟩
      refine ⟨⟨(h1.mpr ⟨hpN, fun i => ?_⟩).1, (h2.mpr ⟨hpN, fun j => ?_⟩).1⟩, hpN⟩
      · simpa using hk (finSumFinEquiv (Sum.inl i))
      · simpa using hk (finSumFinEquiv (Sum.inr j))

theorem isHolZeroSetOn_iUnion {N : Set (ComplexModel m)} {ι : Type*} [Fintype ι] (A : ι → Set (ComplexModel m))
    (hA : ∀ i, IsHolZeroSetOn N (A i)) : IsHolZeroSetOn N (⋃ i, A i) := by
  classical
  have key : ∀ s : Finset ι, IsHolZeroSetOn N (⋃ i ∈ s, A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isHolZeroSetOn_empty N
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hA i).union ih
  simpa using key Finset.univ

theorem thinIn_iUnion {N Q : Set (ComplexModel m)} {ι : Type*} [Fintype ι] (T : ι → Set (ComplexModel m))
    (hT : ∀ i, IsHolZeroSetOn N (T i)) (hthin : ∀ i, ThinIn N Q (T i)) : ThinIn N Q (⋃ i, T i) := by
  classical
  have key : ∀ s : Finset ι, ThinIn N Q (⋃ i ∈ s, T i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using thinIn_empty N Q
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hthin i).union ih (hT i)
  simpa using key Finset.univ

/-- Proper analytic subgerms of an irreducible germ are thin (translated to `p₀`). -/
theorem exists_thinIn_of_irreducible {p₀ : ComplexModel m} {Q B : Set (ComplexModel m)}
    (hQ : IsIrreducibleGerm {w | p₀ + w ∈ Q}) (hB : IsAnalyticGerm {w | p₀ + w ∈ B})
    (hQB : ¬ ∀ᶠ p in 𝓝 p₀, p ∈ Q → p ∈ B) :
    ∃ N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ ThinIn N Q B := by
  have hAB : ¬ ({w | p₀ + w ∈ Q} ≤ᶠ[𝓝 0] {w | p₀ + w ∈ B}) := by
    intro h
    apply hQB
    have ht : Tendsto (fun p : ComplexModel m => p - p₀) (𝓝 p₀) (𝓝 0) :=
      (continuous_id.sub continuous_const).tendsto' p₀ 0 (by simp)
    filter_upwards [ht.eventually h] with p hp hpQ
    have hp' : p₀ + (p - p₀) ∈ Q := by rw [add_sub_cancel]; exact hpQ
    have := hp hp'
    change p₀ + (p - p₀) ∈ B at this
    rwa [add_sub_cancel] at this
  obtain ⟨Ω, hΩ, h0Ω, hthin⟩ := IrreducibleGermLocal.exists_thin_nhds hQ hB hAB
  refine ⟨(fun p => p - p₀) ⁻¹' Ω, hΩ.preimage (continuous_id.sub continuous_const), by simpa using h0Ω, ?_⟩
  intro O hO hON ⟨x, hxO, hxQ⟩
  obtain ⟨y', ⟨hy'O, hy'Q, hy'Ω⟩, hy'B⟩ := hthin ((fun w => p₀ + w) ⁻¹' O)
    (hO.preimage (continuous_const.add continuous_id))
    ⟨x - p₀, by simpa using hxO, by simpa using hxQ, hON hxO⟩
  exact ⟨p₀ + y', ⟨hy'O, hy'Q⟩, hy'B⟩

/-! ### Irreducible pieces of a parameter set -/

/-- **The irreducible pieces of `P` near `p₀`**, as holomorphic zero sets on one neighbourhood, pairwise thin. -/
theorem exists_pieces {p₀ : ComplexModel m} {P : Set (ComplexModel m)} (hP : IsAnalyticNear P p₀) :
    ∃ (r : ℕ) (Pc : Fin r → Set (ComplexModel m)) (N : Set (ComplexModel m)), IsOpen N ∧ p₀ ∈ N ∧
      (∀ i, IsHolZeroSetOn N (Pc i)) ∧ (∀ i, IsIrreducibleGerm {w | p₀ + w ∈ Pc i}) ∧
      (∀ i, Pc i ∩ N ⊆ P) ∧ P ∩ N ⊆ (⋃ i, Pc i) ∧ (∀ i j, i ≠ j → ThinIn N (Pc i) (Pc j)) := by
  classical
  obtain ⟨N₀, hN₀, hp₀N₀, r₀, q, hq, hPq⟩ := hP
  have htr : Tendsto (fun w : ComplexModel m => p₀ + w) (𝓝 0) (𝓝 p₀) :=
    (continuous_const.add continuous_id).tendsto' 0 p₀ (by simp)
  have hPt : IsAnalyticGerm {w | p₀ + w ∈ P} := by
    refine ⟨r₀, fun j w => q j (p₀ + w), fun j => ?_, ?_⟩
    · filter_upwards [htr.eventually (hN₀.mem_nhds hp₀N₀)] with w hw
      exact ((hq j).differentiableAt (hN₀.mem_nhds hw)).comp w
        ((differentiableAt_const _).add differentiableAt_id)
    · filter_upwards [htr.eventually (hN₀.mem_nhds hp₀N₀)] with w hw
      have h := Set.ext_iff.mp hPq (p₀ + w)
      simp only [mem_inter_iff, mem_ofPred_eq] at h
      exact ⟨fun hwP => (h.mp ⟨hwP, hw⟩).2, fun h0 => (h.mpr ⟨hw, h0⟩).1⟩
  obtain ⟨r, Bt, hirr, hle, heq, hpw⟩ := exists_irreducible_decomposition_euclidean hPt
  let Pc : Fin r → Set (ComplexModel m) := fun i => {p | p - p₀ ∈ Bt i}
  have hPcB : ∀ i, {w | p₀ + w ∈ Pc i} = Bt i := fun i => by
    ext w
    simp [Pc]
  have hirr' : ∀ i, IsIrreducibleGerm {w | p₀ + w ∈ Pc i} := fun i => by rw [hPcB]; exact hirr i
  -- one open set near `0` carrying all the germ data
  have hdata : ∀ i, ∃ (s : ℕ) (g : Fin s → ComplexModel m → ℂ),
      ∀ᶠ w in 𝓝 (0 : ComplexModel m), (∀ j, DifferentiableAt ℂ (g j) w) ∧ (w ∈ Bt i ↔ ∀ j, g j w = 0) := by
    intro i
    obtain ⟨s, g, hg, hBg⟩ := (hirr i).1
    exact ⟨s, g, (eventually_all.mpr hg).and hBg⟩
  choose s g hg using hdata
  have hall : ∀ᶠ w in 𝓝 (0 : ComplexModel m), (∀ i, (∀ j, DifferentiableAt ℂ (g i j) w) ∧
      (w ∈ Bt i ↔ ∀ j, g i j w = 0)) ∧ (∀ i, w ∈ Bt i → w ∈ {w | p₀ + w ∈ P}) ∧
      (w ∈ {w | p₀ + w ∈ P} ↔ w ∈ ⋃ i, Bt i) :=
    (eventually_all.mpr hg).and ((eventually_all.mpr hle).and (eventuallyEq_set.mp heq))
  obtain ⟨Ω, hΩsub, hΩ, h0Ω⟩ := eventually_nhds_iff.mp hall
  -- pairwise thinness
  have hthin : ∀ i j, ∃ N' : Set (ComplexModel m), IsOpen N' ∧ p₀ ∈ N' ∧ (i ≠ j → ThinIn N' (Pc i) (Pc j)) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => (h hij).elim⟩
    · have hB : IsAnalyticGerm {w | p₀ + w ∈ Pc j} := by rw [hPcB]; exact (hirr j).1
      have hQB : ¬ ∀ᶠ p in 𝓝 p₀, p ∈ Pc i → p ∈ Pc j := by
        intro h
        apply hpw hij
        filter_upwards [htr.eventually h] with w hw hwi
        have h1 : p₀ + w ∈ Pc i := by
          show p₀ + w - p₀ ∈ Bt i
          rw [add_sub_cancel_left]
          exact hwi
        have h2 := hw h1
        change p₀ + w - p₀ ∈ Bt j at h2
        rw [add_sub_cancel_left] at h2
        exact h2
      obtain ⟨N', hN', hp₀N', hT⟩ := exists_thinIn_of_irreducible (hirr' i) hB hQB
      exact ⟨N', hN', hp₀N', fun _ => hT⟩
  choose N' hN' hp₀N' hthinN' using hthin
  let N : Set (ComplexModel m) := ((fun p => p - p₀) ⁻¹' Ω) ∩ ⋂ i, ⋂ j, N' i j
  have hN : IsOpen N := (hΩ.preimage (continuous_id.sub continuous_const)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hN' i j)
  have hp₀N : p₀ ∈ N := ⟨by simpa using h0Ω, mem_iInter.mpr fun i => mem_iInter.mpr fun j => hp₀N' i j⟩
  have hNΩ : ∀ p ∈ N, p - p₀ ∈ Ω := fun p hp => hp.1
  refine ⟨r, Pc, N, hN, hp₀N, fun i => ?_, hirr', fun i => ?_, ?_, fun i j hij => ?_⟩
  · refine ⟨s i, fun j p => g i j (p - p₀), fun j p hp => ?_, ?_⟩
    · exact (((hΩsub _ (hNΩ p hp)).1 i).1 j).comp p (differentiableAt_id.sub (differentiableAt_const _))
        |>.differentiableWithinAt
    · ext p
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hpi, hpN⟩
        exact ⟨hpN, ((hΩsub _ (hNΩ p hpN)).1 i).2.mp hpi⟩
      · rintro ⟨hpN, h0⟩
        exact ⟨((hΩsub _ (hNΩ p hpN)).1 i).2.mpr h0, hpN⟩
  · rintro p ⟨hpi, hpN⟩
    have := (hΩsub _ (hNΩ p hpN)).2.1 i hpi
    simpa using this
  · rintro p ⟨hpP, hpN⟩
    have hmem : p - p₀ ∈ ⋃ i, Bt i := ((hΩsub _ (hNΩ p hpN)).2.2).mp (by simpa using hpP)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
    exact mem_iUnion.mpr ⟨i, hi⟩
  · exact (hthinN' i j hij).mono fun p hp => mem_iInter.mp (mem_iInter.mp hp.2 i) j

/-! ### The main theorem -/

local instance chartAlgH (d t : ℕ) :
    Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen.basePullback d t).toAlgebra

/-- **`hGF` holds** (Frisch, Th. (II,1) (i)+(ii) with the local criterion): for a relatively exact start `(G, A)`
over a parameter set `P` analytic near `p₀ ∈ P`, the fibre start is exact at `y₀` at every parameter of `P` near `p₀`
off an analytic subset `P''` of `P` which is nowhere dense in `P`. This is verbatim the hypothesis `hGF` of
`HironakaG10RmRelStart.isConstructibleNear_fibreExact_of_hGF`. -/
theorem hGF_holds {t : ℕ} (y₀ : ComplexModel t) (p₀ : ComplexModel m) :
    ∀ P : Set (ComplexModel m), IsAnalyticNear P p₀ → p₀ ∈ P → ∀ {a b c : ℕ}
      (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn → (p₀, y₀) ∈ Wn →
      RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 p₀, p ∈ P → p ∉ P'' → FibreExactAt G A p y₀ := by
  classical
  intro P hP hp₀ a b c A G Wn hWn hpWn hS
  obtain ⟨r, Pc, N₁, hN₁, hp₀N₁, hPcz, hirr, hPcP, hPPc, hthinPc⟩ := exists_pieces hP
  have hA : ∀ i j, HolAt (A i j) (p₀, y₀) := fun i j => holAt_of_differentiableOn hWn (hS.holA i j) hpWn
  have hpiece : ∀ k : Fin r, ∃ g : ComplexModel m → ℂ, HolAt g p₀ ∧
      (∃ N₂ : Set (ComplexModel m), IsOpen N₂ ∧ p₀ ∈ N₂ ∧ DifferentiableOn ℂ g N₂ ∧
        ThinIn N₂ (Pc k) {p | g p = 0}) ∧
      ∀ᶠ p in 𝓝 p₀, p ∈ Pc k → g p ≠ 0 →
        HironakaG10MwWindowFamily.ChartFlat m t A (p, y₀) (baseIdeal (Pc k) p) := by
    intro k
    have hprime : (baseIdeal (Pc k) p₀).IsPrime := (isIrreducibleGerm_iff_isPrime (hirr k).1).mp (hirr k)
    obtain ⟨g, hg, hgnot, hev⟩ := exists_flat_irreducible p₀ y₀ (Pc k) ⟨N₁, hN₁, hp₀N₁, hPcz k⟩ hprime A hA
    have hgt : ∀ᶠ w in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ (fun w => g (p₀ + w)) w := by
      have htr : Tendsto (fun w : ComplexModel m => p₀ + w) (𝓝 0) (𝓝 p₀) :=
        (continuous_const.add continuous_id).tendsto' 0 p₀ (by simp)
      filter_upwards [htr.eventually hg] with w hw
      exact hw.comp w ((differentiableAt_const _).add differentiableAt_id)
    have hB : IsAnalyticGerm {w | p₀ + w ∈ {p | g p = 0}} := isAnalyticGerm_zeroSet hgt
    obtain ⟨N₂, hN₂, hp₀N₂, hT⟩ := exists_thinIn_of_irreducible (hirr k) hB hgnot
    obtain ⟨N₃, hN₃, hp₀N₃, hgN₃⟩ := hg.exists_isOpen
    exact ⟨g, hg, ⟨N₂ ∩ N₃, hN₂.inter hN₃, ⟨hp₀N₂, hp₀N₃⟩, hgN₃.mono inter_subset_right,
      hT.mono inter_subset_left⟩, hev⟩
  choose g hg hN₂data hev using hpiece
  choose N₂ hN₂ hp₀N₂ hgN₂ hthinG using hN₂data
  let N : Set (ComplexModel m) := N₁ ∩ ⋂ k, N₂ k
  have hN : IsOpen N := hN₁.inter (isOpen_iInter_of_finite hN₂)
  have hp₀N : p₀ ∈ N := ⟨hp₀N₁, mem_iInter.mpr hp₀N₂⟩
  have hNN₁ : N ⊆ N₁ := inter_subset_left
  have hNN₂ : ∀ k, N ⊆ N₂ k := fun k p hp => mem_iInter.mp hp.2 k
  have hPczN : ∀ k, IsHolZeroSetOn N (Pc k) := fun k => (hPcz k).mono hNN₁
  have hgz : ∀ k, IsHolZeroSetOn N {p | g k p = 0} := fun k =>
    ⟨1, fun _ => g k, fun _ => (hgN₂ k).mono (hNN₂ k), by ext p; simp [and_comm]⟩
  let D : Fin r × Fin r → Set (ComplexModel m) := fun ij => if ij.1 = ij.2 then ∅ else Pc ij.1 ∩ Pc ij.2
  have hDz : ∀ ij, IsHolZeroSetOn N (D ij) := by
    intro ij
    by_cases h : ij.1 = ij.2
    · simp only [D, if_pos h]; exact isHolZeroSetOn_empty N
    · simp only [D, if_neg h]; exact isHolZeroSetOn_inter (hPczN ij.1) (hPczN ij.2)
  let P'' : Set (ComplexModel m) := (⋃ k, Pc k ∩ {p | g k p = 0}) ∪ ⋃ ij, D ij
  have hmemD : ∀ {x : ComplexModel m} {i j : Fin r}, i ≠ j → x ∈ Pc i → x ∈ Pc j → x ∈ P'' := by
    intro x i j hij hi hj
    refine Or.inr (mem_iUnion.mpr ⟨(i, j), ?_⟩)
    simp only [D, if_neg hij]
    exact ⟨hi, hj⟩
  have hP''sub : ∀ x ∈ P'', ∃ k, x ∈ Pc k := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨k, hk, -⟩ := mem_iUnion.mp hx
      exact ⟨k, hk⟩
    · obtain ⟨ij, hij⟩ := mem_iUnion.mp hx
      by_cases h : ij.1 = ij.2
      · simp only [D, if_pos h] at hij; exact hij.elim
      · simp only [D, if_neg h] at hij; exact ⟨ij.1, hij.1⟩
  refine ⟨P'', N, hN, hp₀N, ?_, ?_, ?_, ?_⟩
  · exact (isHolZeroSetOn_iUnion _ fun k => isHolZeroSetOn_inter (hPczN k) (hgz k)).union (isHolZeroSetOn_iUnion D hDz)
  · rintro x ⟨hx, hxN⟩
    obtain ⟨k, hk⟩ := hP''sub x hx
    exact hPcP k ⟨hk, hNN₁ hxN⟩
  · intro U hU hUN ⟨x, hxU, hxP⟩ hsub
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hPPc ⟨hxP, hNN₁ (hUN hxU)⟩)
    -- the thin set of `Pc k`
    let T : Set (ComplexModel m) := {p | g k p = 0} ∪ ⋃ j, (if j = k then ∅ else Pc j)
    have hTthin : ThinIn N (Pc k) T := by
      refine ((hthinG k).mono (hNN₂ k)).union ?_ (hgz k)
      refine thinIn_iUnion _ (fun j => ?_) (fun j => ?_)
      · by_cases h : j = k
        · simp only [if_pos h]; exact isHolZeroSetOn_empty N
        · simp only [if_neg h]; exact hPczN j
      · by_cases h : j = k
        · simp only [if_pos h]; exact thinIn_empty N _
        · simp only [if_neg h]; exact (hthinPc k j (Ne.symm h)).mono hNN₁
    obtain ⟨y, ⟨hyU, hyk⟩, hyT⟩ := hTthin U hU hUN ⟨x, hxU, hk⟩
    have hyP'' : y ∈ P'' := hsub ⟨hyU, hPcP k ⟨hyk, hNN₁ (hUN hyU)⟩⟩
    apply hyT
    rcases hyP'' with hy | hy
    · obtain ⟨l, hl, hgl⟩ := mem_iUnion.mp hy
      by_cases h : l = k
      · subst h; exact Or.inl hgl
      · exact Or.inr (mem_iUnion.mpr ⟨l, by simp only [if_neg h]; exact hl⟩)
    · obtain ⟨ij, hij⟩ := mem_iUnion.mp hy
      by_cases h : ij.1 = ij.2
      · simp only [D, if_pos h] at hij; exact hij.elim
      · simp only [D, if_neg h] at hij
        by_cases h1 : ij.1 = k
        · have h2 : ij.2 ≠ k := fun h2 => h (h1.trans h2.symm)
          exact Or.inr (mem_iUnion.mpr ⟨ij.2, by simp only [if_neg h2]; exact hij.2⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨ij.1, by simp only [if_neg h1]; exact hij.1⟩)
  · have hWev : ∀ᶠ p in 𝓝 p₀, (p, y₀) ∈ Wn := by
      have ht : Tendsto (fun p : ComplexModel m => (p, y₀)) (𝓝 p₀) (𝓝 (p₀, y₀)) :=
        (continuous_id.prodMk continuous_const).tendsto p₀
      exact ht.eventually (hWn.mem_nhds hpWn)
    filter_upwards [eventually_all.mpr hev, hN.mem_nhds hp₀N, hWev] with p hevp hpN hpW hpP hpP''
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hPPc ⟨hpP, hNN₁ hpN⟩)
    have hgk : g k p ≠ 0 := fun h0 => hpP'' (Or.inl (mem_iUnion.mpr ⟨k, hk, h0⟩))
    have hother : ∀ j, j ≠ k → p ∉ Pc j := fun j hjk hj => hpP'' (hmemD hjk hj hk)
    have hflat := hevp k hk hgk
    -- near `p` the set `P` is `Pc k`
    have hloc : ∀ᶠ x in 𝓝 p, x ∈ N ∧ ∀ j, j ≠ k → x ∉ Pc j := by
      refine Filter.Eventually.and (hN.mem_nhds hpN) (eventually_all.mpr fun j => ?_)
      by_cases hjk : j = k
      · exact Eventually.of_forall fun _ h => (h hjk).elim
      · filter_upwards [((hPczN j).isOpen_sdiff hN subset_rfl).mem_nhds ⟨hpN, hother j hjk⟩] with x hx _
        exact hx.2
    have hbase : baseIdeal (Pc k) p = baseIdeal P p := by
      apply vanishingIdeal_congr
      have ht : Tendsto (fun w : ComplexModel m => p + w) (𝓝 0) (𝓝 p) :=
        (continuous_const.add continuous_id).tendsto' 0 p (by simp)
      filter_upwards [ht.eventually hloc] with w hw
      apply propext
      change p + w ∈ Pc k ↔ p + w ∈ P
      constructor
      · intro h
        exact hPcP k ⟨h, hNN₁ hw.1⟩
      · intro h
        obtain ⟨l, hl⟩ := mem_iUnion.mp (hPPc ⟨h, hNN₁ hw.1⟩)
        by_cases hlk : l = k
        · exact hlk ▸ hl
        · exact (hw.2 l hlk hl).elim
    rw [hbase] at hflat
    have hAp : ∀ i j, HolAt (A i j) (p, y₀) := fun i j => holAt_of_differentiableOn hWn (hS.holA i j) hpW
    have hGp : ∀ j k, HolAt (G j k) (p, y₀) := fun j k => holAt_of_differentiableOn hWn (hS.holG j k) hpW
    have hst := exactStartMod_of_relExactStartOn hS hWn hpW hpP
    have hst' : Hironaka.Analytic.Unibranch.HironakaG10TmLocalFlatness.ExactStartModAt m t (baseIdeal P p) G A (p, y₀) := by
      unfold Hironaka.Analytic.Unibranch.HironakaG10TmLocalFlatness.ExactStartModAt
      exact ⟨hst.1, hst.2⟩
    have hiff := Hironaka.Analytic.Unibranch.HironakaG10TmLocalFlatness.chartFlat_iff_fibreExactAt m t (baseIdeal P p)
      (baseIdeal_le_maximalIdeal hpP) A G (p, y₀) hAp hGp hst'
    exact hiff.mp hflat

/-- **Route G at a fixed fibre point, unconditionally** (Frisch (III,6)+(IV,5)): the parameters `p ∈ P` at which
the fibre complex of `(u, v)` is exact at `y₀` form a set constructible near `p₀`. -/
theorem isConstructibleNear_fibreExact {t : ℕ} (y₀ : ComplexModel t) (p₀ : ComplexModel m)
    {a b n : ℕ} (u : Fin b → Fin n → ComplexModel m × ComplexModel t → ℂ)
    (v : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
    (hu : ∀ j l, HolAt (u j l) (p₀, y₀)) (hv : ∀ i j, HolAt (v i j) (p₀, y₀))
    (P : Set (ComplexModel m)) (hP : IsAnalyticNear P p₀)
    (hcomp : ∀ᶠ q in 𝓝 (p₀, y₀), q.1 ∈ P → ∀ i l, ∑ j, v i j q * u j l q = 0) :
    IsConstructibleNear {s | s ∈ P ∧ FibreExactAt u v s y₀} p₀ :=
  Hironaka.Analytic.Unibranch.HironakaG10RmRelStart.isConstructibleNear_fibreExact_of_hGF y₀ p₀ (hGF_holds y₀ p₀)
    u v hu hv P hP hcomp

/-- **Item 2 (route G), varying fibre points, unconditionally.** -/
theorem isConstructibleNear_fibreExact_varying {t d : ℕ}
    (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t)
    (T : Set (ComplexModel d)) (s₀ : ComplexModel d) (x₀ : ComplexModel t) (hT : IsAnalyticNear T s₀)
    {a b n : ℕ} (u : Fin b → Fin n → ComplexModel d × ComplexModel t → ℂ)
    (v : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (hu : ∀ j l, HolAt (u j l) (s₀, x₀)) (hv : ∀ i j, HolAt (v i j) (s₀, x₀))
    (hcomp : ∀ᶠ q in 𝓝 (s₀, x₀), q.1 ∈ T → ∀ i l, ∑ j, v i j q * u j l q = 0) :
    IsConstructibleNear (e ⁻¹' {q | q.1 ∈ T ∧ FibreExactAt u v q.1 q.2}) (e.symm (s₀, x₀)) :=
  Hironaka.Analytic.Unibranch.HironakaG10RmRelStart.isConstructibleNear_fibreExact_varying_of_hGF e T s₀ x₀ hT
    (hGF_holds 0 (e.symm (s₀, x₀))) u v hu hv hcomp

end

end Hironaka.Analytic.Unibranch.HironakaG10GnHGF
