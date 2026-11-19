import Hironaka.Analytic.Unibranch.HironakaG10FrAmbientIV7
import Hironaka.Analytic.Unibranch.HironakaG10RmRelStart
import Hironaka.Analytic.Unibranch.HironakaG10GfModStart
import Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
import Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily

/-!
# Frisch's Theorem (IV,9) in a chart (ASM step 3a)

J. Frisch, *Points de platitude d'un morphisme d'espaces analytiques complexes*, Invent. Math. 4 (1967),
Th. (IV,9) (p. 133), read in a chart: for a parameter set `T ⊆ ℂᵈ` analytic near `s₀` and a matrix `F` of
holomorphic functions near `(s₀, z₀) ∈ ℂᵈ × ℂᵗ`, the **chart non-flat set**
`{(s, z) | s ∈ T, coker F not flat over 𝒪_d ⧸ I_T at (s, z)}` (`HironakaG10MwWindowFamily.ChartFlat` over the base
ideal `HironakaG10GfModStart.baseIdeal T s`) is analytic near `(s₀, z₀)` (read in `ℂ^{d+t}` through
`splitModel d t`): **`exists_opens_chartNonflat`**.

Proof (Frisch's): take a relatively exact start `(G, F)` over `T` (`HironakaG10RmRelStart.exists_relExactStartOn`);
by the chart local criterion of flatness (item 1, explicit hypothesis `h1`) the non-flat set is, near the point,
`{s ∈ T, fibre start not exact at z}`; it is constructible (route G at varying fibre points,
`HironakaG10RmRelStart.isConstructibleNear_fibreExact_varying_of_hGF`, with the generic-flatness hypothesis `hGF`;
complement and intersection: `IsConstructibleNear.compl`, `.inter`), relatively closed (Douady's openness of the
relative flat locus, `HironakaG10LocEuclideanCartan.eventually_relFibreFlatAt`), hence analytic (Lemma (IV,7),
`HironakaG10FrAmbientIV7.exists_opens_isComplexAnalyticSubset`).

Explicit hypotheses (no named `Prop`): `hGF` (Frisch Th. (II,1), lane G10GN) and `h1` (the chart local criterion
for relatively exact starts: lane G10LF's `chartFlat_iff_fibreExactAt` composed with G10GF's
`exactStartMod_of_relExactStartOn`).

Lane G10R3 (continuing lane G10FR), run 0081. Blueprint: `hironaka-g10fr-chart-iv9.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10FrChartIV9

open Hironaka Hironaka
open OkaRelationSheaf OkaGermBridge HironakaG10LocSheafExact HironakaG10LocFibreOpen HironakaG10LocRelative
  Hironaka.Analytic.Unibranch.HironakaG10FrRouteG Hironaka.Analytic.Unibranch.HironakaG10FrAmbientIV7
  Hironaka.Analytic.Unibranch.HironakaG10RmRelStart Hironaka.Analytic.Unibranch.HironakaG10GfModStart
  Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen

noncomputable section

variable {m : ℕ}

/-! ### Boolean operations on constructible germs -/

/-- Holomorphic zero sets on `N` are closed under intersection. -/
theorem isHolZeroSetOn_inter {N A B : Set (ComplexModel m)} (hA : IsHolZeroSetOn N A)
    (hB : IsHolZeroSetOn N B) : IsHolZeroSetOn N (A ∩ B) := by
  obtain ⟨r, g, hg, hgA⟩ := hA
  obtain ⟨s, h, hh, hhB⟩ := hB
  refine ⟨r + s, Fin.append g h, fun k => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left]; exact hg i
    · rw [Fin.append_right]; exact hh j
  · ext p
    have hA' := Set.ext_iff.mp hgA p
    have hB' := Set.ext_iff.mp hhB p
    simp only [mem_inter_iff, mem_ofPred_eq] at hA' hB' ⊢
    have hall : (∀ k, Fin.append g h k p = 0) ↔ (∀ i, g i p = 0) ∧ ∀ j, h j p = 0 := by
      constructor
      · intro hk
        refine ⟨fun i => ?_, fun j => ?_⟩
        · have := hk (Fin.castAdd s i)
          rwa [Fin.append_left] at this
        · have := hk (Fin.natAdd r j)
          rwa [Fin.append_right] at this
      · rintro ⟨hi, hj⟩ k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · rw [Fin.append_left]; exact hi i
        · rw [Fin.append_right]; exact hj j
    rw [hall]
    constructor
    · rintro ⟨⟨hpA, hpB⟩, hpN⟩
      exact ⟨hpN, (hA'.mp ⟨hpA, hpN⟩).2, (hB'.mp ⟨hpB, hpN⟩).2⟩
    · rintro ⟨hpN, hi, hj⟩
      exact ⟨⟨(hA'.mpr ⟨hpN, hi⟩).1, (hB'.mpr ⟨hpN, hj⟩).1⟩, hpN⟩

/-- The empty set is a holomorphic zero set. -/
theorem isHolZeroSetOn_empty (N : Set (ComplexModel m)) : IsHolZeroSetOn N ∅ :=
  ⟨1, fun _ _ => 1, fun _ => differentiableOn_const _, by ext p; simp⟩

section Constructible

variable {E F : Set (ComplexModel m)} {p₀ : ComplexModel m}

/-- Intersections of constructible germs are constructible. -/
theorem isConstructibleNear_inter (hE : IsConstructibleNear E p₀) (hF : IsConstructibleNear F p₀) :
    IsConstructibleNear (E ∩ F) p₀ := by
  classical
  obtain ⟨N, hN, hpN, Q, hQ, hEQ⟩ := hE
  obtain ⟨N', hN', hpN', Q', hQ', hFQ⟩ := hF
  refine ⟨N ∩ N', hN.inter hN', ⟨hpN, hpN'⟩,
    (Q ×ˢ Q').image (fun qq => (qq.1.1 ∩ qq.2.1, qq.1.2 ∪ qq.2.2)), ?_, ?_⟩
  · intro r hr
    obtain ⟨⟨q, q'⟩, hqq, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hq, hq'⟩ := Finset.mem_product.mp hqq
    exact ⟨isHolZeroSetOn_inter ((hQ q hq).1.mono inter_subset_left)
        ((hQ' q' hq').1.mono inter_subset_right),
      ((hQ q hq).2.mono inter_subset_left).union ((hQ' q' hq').2.mono inter_subset_right)⟩
  · ext p
    have h1 := Set.ext_iff.mp hEQ p
    have h2 := Set.ext_iff.mp hFQ p
    simp only [mem_inter_iff, mem_iUnion, Set.mem_sdiff, exists_prop, Prod.exists] at h1 h2
    simp only [mem_inter_iff, Finset.set_biUnion_finset_image, mem_iUnion, Set.mem_sdiff, mem_union,
      Finset.mem_product, exists_prop, Prod.exists]
    constructor
    · rintro ⟨⟨hpE, hpF⟩, hpN, hpN'⟩
      obtain ⟨⟨q₁, q₂, hq, hp1, hp2⟩, -⟩ := h1.mp ⟨hpE, hpN⟩
      obtain ⟨⟨q₁', q₂', hq', hp1', hp2'⟩, -⟩ := h2.mp ⟨hpF, hpN'⟩
      exact ⟨⟨q₁, q₂, q₁', q₂', ⟨hq, hq'⟩, ⟨hp1, hp1'⟩, fun h => h.elim hp2 hp2'⟩, hpN, hpN'⟩
    · rintro ⟨⟨q₁, q₂, q₁', q₂', ⟨hq, hq'⟩, ⟨hp1, hp1'⟩, hn⟩, hpN, hpN'⟩
      exact ⟨⟨(h1.mpr ⟨⟨q₁, q₂, hq, hp1, fun h => hn (Or.inl h)⟩, hpN⟩).1,
        (h2.mpr ⟨⟨q₁', q₂', hq', hp1', fun h => hn (Or.inr h)⟩, hpN'⟩).1⟩, hpN, hpN'⟩

/-- `univ` is constructible near every point. -/
theorem isConstructibleNear_univ (p₀ : ComplexModel m) :
    IsConstructibleNear (univ : Set (ComplexModel m)) p₀ :=
  IsConstructibleNear.of_sdiff isOpen_univ (mem_univ p₀) (isHolZeroSetOn_univ _) (isHolZeroSetOn_empty _) (by simp)

/-- Complements of constructible germs are constructible. -/
theorem isConstructibleNear_compl (hE : IsConstructibleNear E p₀) : IsConstructibleNear Eᶜ p₀ := by
  classical
  obtain ⟨N, hN, hpN, Q, hQ, hEQ⟩ := hE
  -- every finite intersection of complements of normal-form pieces is constructible
  have key : ∀ Q' : Finset (Set (ComplexModel m) × Set (ComplexModel m)),
      (∀ q ∈ Q', IsHolZeroSetOn N q.1 ∧ IsHolZeroSetOn N q.2) →
      IsConstructibleNear (⋂ q ∈ Q', (q.1 \ q.2)ᶜ) p₀ := by
    intro Q'
    induction Q' using Finset.induction_on with
    | empty => intro _; simpa using isConstructibleNear_univ p₀
    | insert q Q' hq ih =>
      intro hQ'
      rw [Finset.set_biInter_insert]
      refine isConstructibleNear_inter ?_ (ih fun q' hq' => hQ' q' (Finset.mem_insert_of_mem hq'))
      have hq' := hQ' q (Finset.mem_insert_self q Q')
      have h1 : IsConstructibleNear (Set.univ \ q.1) p₀ :=
        IsConstructibleNear.of_sdiff hN hpN (isHolZeroSetOn_univ _) hq'.1 rfl
      have h2 : IsConstructibleNear q.2 p₀ :=
        IsConstructibleNear.of_sdiff hN hpN hq'.2 (isHolZeroSetOn_empty _) (by simp)
      have heq : (q.1 \ q.2)ᶜ = (Set.univ \ q.1) ∪ q.2 := by
        ext p; simp only [mem_compl_iff, Set.mem_sdiff, mem_union, mem_univ, true_and]; tauto
      rw [heq]
      exact IsConstructibleNear.union h1 h2
  refine IsConstructibleNear.congr (key Q hQ) hN hpN ?_
  ext p
  have h := Set.ext_iff.mp hEQ p
  simp only [mem_inter_iff, mem_iUnion, Set.mem_sdiff, exists_prop, Prod.exists] at h
  simp only [mem_inter_iff, mem_iInter, mem_compl_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨hp, hpN⟩
    refine ⟨fun hpE => ?_, hpN⟩
    obtain ⟨⟨q₁, q₂, hq, hp1, hp2⟩, -⟩ := h.mp ⟨hpE, hpN⟩
    exact hp (q₁, q₂) hq ⟨hp1, hp2⟩
  · rintro ⟨hpE, hpN⟩
    refine ⟨fun q hq hpq => hpE (h.mpr ⟨⟨q.1, q.2, hq, hpq⟩, hpN⟩).1, hpN⟩

/-- Differences of constructible germs are constructible. -/
theorem isConstructibleNear_sdiff (hE : IsConstructibleNear E p₀) (hF : IsConstructibleNear F p₀) :
    IsConstructibleNear (E \ F) p₀ := by
  rw [Set.sdiff_eq]
  exact isConstructibleNear_inter hE (isConstructibleNear_compl hF)

end Constructible

/-! ### Analytic sets of open subsets of `ℂᵈ` are analytic near their points -/

/-- An analytic subset of an open `U ⊆ ℂᵈ` (as a manifold) is analytic near every point of `U` (in `ℂᵈ`). -/
theorem isAnalyticNear_image_val {d : ℕ} {U : Opens (ComplexModel d)} {S : Set U}
    (hS : IsComplexAnalyticSubset (n := d) S) (u : U) :
    IsAnalyticNear (Subtype.val '' S) (u : ComplexModel d) := by
  obtain ⟨P⟩ := hS u
  refine ⟨P.coordinateNeighborhood, P.isOpen_coordinateNeighborhood, ?_, P.generatorCount,
    P.generator, P.generator_holomorphic, ?_⟩
  · have := P.center_mem_coordinateNeighborhood
    rwa [complexChartAt_opens_apply U u u] at this
  · ext p
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨y, hyS, rfl⟩, hpN⟩
      refine ⟨hpN, ?_⟩
      have h := (P.zeroLocus (y := y) (mem_complexChartAt_opens_source U u y)
        (by rw [complexChartAt_opens_apply U u y]; exact hpN)).mp hyS
      rwa [complexChartAt_opens_apply U u y] at h
    · rintro ⟨hpN, hp0⟩
      have hpU : p ∈ U := mem_of_mem_complexChartAt_opens_target U u
        (P.coordinateNeighborhood_subset_target hpN)
      refine ⟨⟨⟨p, hpU⟩, ?_, rfl⟩, hpN⟩
      refine (P.zeroLocus (y := ⟨p, hpU⟩) (mem_complexChartAt_opens_source U u _)
        (by rw [complexChartAt_opens_apply U u]; exact hpN)).mpr ?_
      rw [complexChartAt_opens_apply U u]
      exact hp0

/-- The cylinder over a set analytic near `s₀` is constructible near every point over `s₀`. -/
theorem isConstructibleNear_cylinder {d t : ℕ} (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t)
    {T : Set (ComplexModel d)} {s₀ : ComplexModel d} (hT : IsAnalyticNear T s₀) (z₀ : ComplexModel t) :
    IsConstructibleNear (e ⁻¹' {q | q.1 ∈ T}) (e.symm (s₀, z₀)) := by
  obtain ⟨N, hN, hsN, r, g, hg, hgT⟩ := hT
  have hcont : Continuous fun w : ComplexModel m => (e w).1 := continuous_fst.comp e.continuous
  refine IsConstructibleNear.of_sdiff (A := e ⁻¹' {q | q.1 ∈ T}) (B := ∅)
    (hN.preimage hcont) (by simpa using hsN) ⟨r, fun i w => g i (e w).1, fun i => ?_, ?_⟩
    (isHolZeroSetOn_empty _) (by simp)
  · intro w hw
    have hd : DifferentiableAt ℂ (fun w : ComplexModel m => (e w).1) w :=
      (e.differentiableAt (x := w)).fst
    exact ((hg i _ hw).differentiableAt (hN.mem_nhds hw)).comp w hd |>.differentiableWithinAt
  · ext w
    have h := Set.ext_iff.mp hgT (e w).1
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage] at h ⊢
    exact h

/-! ### The chart non-flat set -/

/-- **Frisch Th. (IV,9) in a chart.**  For `T ⊆ ℂᵈ` analytic near `s₀` and `F` holomorphic near `(s₀, z₀)`, the
chart non-flat set `{q | q.1 ∈ T ∧ ¬ ChartFlat d t F q (baseIdeal T q.1)}` is analytic in an open neighbourhood of
`(s₀, z₀)` (read in `ℂ^{d+t}`), given generic flatness at a fixed fibre point (`hGF`, Frisch Th. (II,1)) and the
chart local criterion for relatively exact starts (`h1`, item 1). -/
theorem exists_opens_chartNonflat {d t : ℕ}
    (h1 : ∀ {a b c : ℕ} {T : Set (ComplexModel d)} {W : Set (ComplexModel d × ComplexModel t)}
      {G : Fin b → Fin c → ComplexModel d × ComplexModel t → ℂ}
      {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}, RelExactStartOn T W G F → IsOpen W →
      ∀ {p : ComplexModel d × ComplexModel t}, p ∈ W → p.1 ∈ T →
        (ChartFlat d t F p (baseIdeal T p.1) ↔ FibreExactAt G F p.1 p.2))
    {T : Set (ComplexModel d)} {s₀ : ComplexModel d} {z₀ : ComplexModel t} (hT : IsAnalyticNear T s₀)
    (hGF : ∀ P : Set (ComplexModel (d + t)), IsAnalyticNear P ((splitModel d t).symm (s₀, z₀)) →
      (splitModel d t).symm (s₀, z₀) ∈ P →
      ∀ {a b c : ℕ} (A : Fin a → Fin b → ComplexModel (d + t) × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel (d + t) × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel (d + t) × ComplexModel t)), IsOpen Wn →
      ((splitModel d t).symm (s₀, z₀), (0 : ComplexModel t)) ∈ Wn → RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel (d + t)), IsOpen N ∧ (splitModel d t).symm (s₀, z₀) ∈ N ∧
        IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel (d + t)), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 ((splitModel d t).symm (s₀, z₀)), p ∈ P → p ∉ P'' → FibreExactAt G A p 0)
    {a b : ℕ} (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (hF : ∀ i j, HolAt (F i j) (s₀, z₀)) :
    ∃ U : Opens (ComplexModel (d + t)), (splitModel d t).symm (s₀, z₀) ∈ U ∧
      IsComplexAnalyticSubset (n := d + t) ((↑) ⁻¹' ((splitModel d t) ⁻¹'
        {q | q.1 ∈ T ∧ ¬ ChartFlat d t F q (baseIdeal T q.1)}) : Set U) := by
  classical
  set e := splitModel d t with he
  set w₀ := e.symm (s₀, z₀) with hw₀
  have hew₀ : e w₀ = (s₀, z₀) := by simp [hw₀]
  -- a relatively exact start over `T`
  obtain ⟨c, G, Wn, hWn, hp₀, hst⟩ := exists_relExactStartOn z₀ hT F hF
  have hG : ∀ j k, HolAt (G j k) (s₀, z₀) := fun j k => holAt_of_differentiableOn hWn (hst.holG j k) hp₀
  have hcomp : ∀ᶠ q in 𝓝 (s₀, z₀), q.1 ∈ T → ∀ i l, ∑ j, F i j q * G j l q = 0 := by
    filter_upwards [hWn.mem_nhds hp₀] with q hq hqT i l
    exact hst.comp i l q hq hqT
  -- constructibility of the non-exact set
  have hEx := isConstructibleNear_fibreExact_varying_of_hGF e T s₀ z₀ hT hGF G F hG hF hcomp
  set E : Set (ComplexModel (d + t)) := e ⁻¹' {q | q.1 ∈ T ∧ ¬ FibreExactAt G F q.1 q.2} with hEdef
  have hE : IsConstructibleNear E w₀ := by
    have h := isConstructibleNear_sdiff (isConstructibleNear_cylinder e hT z₀) hEx
    have heq : e ⁻¹' {q | q.1 ∈ T} \ e ⁻¹' {q | q.1 ∈ T ∧ FibreExactAt G F q.1 q.2} = E := by
      ext w
      simp only [hEdef, Set.mem_sdiff, mem_preimage, mem_ofPred_eq, not_and]
      tauto
    rwa [heq] at h
  -- relative closedness
  obtain ⟨N, hN, hs₀N, r, g, hg, hgT⟩ := hT
  have hTN : ∀ s ∈ N, (s ∈ T ↔ ∀ i, g i s = 0) := by
    intro s hs
    have h := Set.ext_iff.mp hgT s
    simp only [mem_inter_iff, mem_ofPred_eq] at h
    exact ⟨fun hsT => (h.mp ⟨hsT, hs⟩).2, fun h0 => (h.mpr ⟨hs, h0⟩).1⟩
  set Ω : Set (ComplexModel (d + t)) := e ⁻¹' (Wn ∩ {q | q.1 ∈ N}) with hΩdef
  have hcont1 : Continuous fun w : ComplexModel (d + t) => (e w).1 := continuous_fst.comp e.continuous
  have hΩo : IsOpen Ω := (hWn.inter (hN.preimage continuous_fst)).preimage e.continuous
  have hw₀Ω : w₀ ∈ Ω := by
    show e w₀ ∈ Wn ∩ {q | q.1 ∈ N}
    rw [hew₀]
    exact ⟨hp₀, hs₀N⟩
  have hcl : closure (E ∩ Ω) ∩ Ω ⊆ E := by
    rintro w ⟨hwcl, hwΩ⟩
    have hwWn : e w ∈ Wn := hwΩ.1
    have hwN : (e w).1 ∈ N := hwΩ.2
    -- the first coordinate lies in `T`
    have hwT : (e w).1 ∈ T := by
      refine (hTN _ hwN).mpr fun i => ?_
      by_contra hne
      have hgc : ContinuousOn (fun w' => g i (e w').1) Ω :=
        (hg i).continuousOn.comp hcont1.continuousOn fun w' hw' => hw'.2
      have hO : IsOpen (Ω ∩ (fun w' => g i (e w').1) ⁻¹' {0}ᶜ) :=
        hgc.isOpen_inter_preimage hΩo isOpen_compl_singleton
      obtain ⟨w', ⟨hw'Ω, hw'g⟩, hw'E, -⟩ := mem_closure_iff.mp hwcl _ hO ⟨hwΩ, hne⟩
      exact hw'g ((hTN _ hw'Ω.2).mp hw'E.1 i)
    refine ⟨hwT, fun hex => ?_⟩
    -- flatness is open (Douady)
    have hflat : RelFibreFlatAt T F (e w) := ⟨c, G, Wn, hWn, hwWn, hst, hex⟩
    have hev := HironakaG10LocEuclideanCartan.eventually_relFibreFlatAt T F hwT hflat
    have hV : e ⁻¹' {q | q.1 ∈ T → RelFibreFlatAt T F q} ∈ 𝓝 w :=
      e.continuous.continuousAt.preimage_mem_nhds hev
    obtain ⟨V, hVsub, hVo, hwV⟩ := mem_nhds_iff.mp hV
    obtain ⟨w', hw'V, hw'E, hw'Ω⟩ := mem_closure_iff.mp hwcl V hVo hwV
    have hrel := hVsub hw'V hw'E.1
    exact hw'E.2 (((relFibreFlatAt_iff_forall T hw'E.1).mp hrel).2 c G Wn hWn hw'Ω.1 hst)
  -- Lemma (IV,7)
  obtain ⟨U, hw₀U, hU⟩ := exists_opens_isComplexAnalyticSubset hE hΩo hw₀Ω hcl
  -- the chart non-flat set agrees with `E` on `e⁻¹ Wn`
  let V : Opens (ComplexModel (d + t)) := ⟨e ⁻¹' Wn, hWn.preimage e.continuous⟩
  refine ⟨U ⊓ V, ⟨hw₀U, by show e w₀ ∈ Wn; rw [hew₀]; exact hp₀⟩, ?_⟩
  have hincl : ContMDiff 𝓘(ℂ, ComplexModel (d + t)) 𝓘(ℂ, ComplexModel (d + t)) ∞
      (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) := contMDiff_inclusion inf_le_left
  have hset : ((↑) ⁻¹' (e ⁻¹' {q | q.1 ∈ T ∧ ¬ ChartFlat d t F q (baseIdeal T q.1)}) :
      Set (U ⊓ V : Opens (ComplexModel (d + t)))) =
      Opens.inclusion (inf_le_left : U ⊓ V ≤ U) ⁻¹' ((↑) ⁻¹' E : Set U) := by
    ext w
    have hwWn : e (w : ComplexModel (d + t)) ∈ Wn := w.property.2
    simp only [mem_preimage, mem_ofPred_eq, hEdef]
    change ((e w).1 ∈ T ∧ ¬ ChartFlat d t F (e w) (baseIdeal T (e w).1)) ↔
      ((e w).1 ∈ T ∧ ¬ FibreExactAt G F (e w).1 (e w).2)
    constructor
    · rintro ⟨hT', hnf⟩
      exact ⟨hT', fun hex => hnf ((h1 hst hWn hwWn hT').mpr hex)⟩
    · rintro ⟨hT', hne⟩
      exact ⟨hT', fun hf => hne ((h1 hst hWn hwWn hT').mp hf)⟩
  rw [hset]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hincl hU

end

end Hironaka.Analytic.Unibranch.HironakaG10FrChartIV9
