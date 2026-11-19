import Hironaka.Invariant.GeneralValueOrderZero
import Hironaka.Analytic.TowerPreimageCompact
import Hironaka.Invariant.StepOnePhase

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The phases of a canonical segment on the side of the order of the nonmonomial part

Hironaka phase H2 (TN3), for the per-sequence local finiteness of the general step's value (human decision I-1139 (b));
claim I-0977 C-0211 (z5b).  Blueprint `bcalc:nonmonomial-order-global-phase` (chapter `blowup-calculus.tex`).  Sources:
Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol` (the order of the nonmonomial part does not
increase; while it stays `o`, the companion ideal of order `o` is resolved, "then we repeat the procedure"); Bierstone--Milman
2008 (`bierstone-milman08-functoriality`), Step II.

The value of the general step begins with the order `ν` of the nonmonomial part.  Along a canonical segment the nonempty centres
are maximum loci, so their orders form the sequence of phases: it never increases, and over a compact set it is bounded.  This
module proves, for every value function `f` whose order dominates `ν` (`NonmonomialOrderCanonical.OrdMonotone`), with `𝔪` in
the domain and `n > 0`:

* **the phase is absorbing** (`nmOrd_le_append_of_le`, `nmOrd_proj_eq_of_le`): if `ν ≤ o` on the cosupport at a stage `T₀`, then
  along every canonical test extension `T₀ S` the order stays `≤ o`, and a point of order `o` lies over a point of order `o` of
  the cosupport at `T₀`;
* **the run of a point of order `o` started at or before `T₀`** (`ordRegime_and_length_le_regimeRun_of_le`): such a point is in
  the regime `OrdRegime 𝔪 o` and its run is at least the length of `S`; and the cosupport at `T₀` lies in the mask
  `ordMask 𝔪_{T₀} o` (`cosupp_subset_ordMask_of_le`), the open set on which the companion ideal of order `o` is formed;
* **phase entry** (`nmOrd_le_of_mem_centre`): a nonempty centre of a canonical step bounds the order on the cosupport before it;
  **the orders of the nonempty centres never increase** (`pairwise_centreValues_nmOrd`, with `StepOnePhase.centreValues` of
  `ν`) and bound the orders on every later cosupport;
* **one bound over a compact set** (`exists_centre_nmOrd_le_of_isCompact`): for compact `K` there is `q` bounding the order of
  every point of every nonempty centre meeting the preimage of `K`, along all canonical test segments;
* **the monomial phase of the general value** (`genInv_snd_of_fst_eq_zero`, `not_strictAnti_zero_inl`): a value of order `0` is
  `(0, inl γ)`, and no sequence of such values strictly decreases forever (`γ`'s values are well-founded,
  `MonomialInvariant.wellFoundedLT_val`); `wellFoundedLT_genValue`: the values of the general step are well-founded when those of
  the maximal-order value are.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderGlobalPhase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MonomialInvariant Hironaka.MonomialStepAlong
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.StepOneRegime Hironaka.StepOnePhase
  Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime
  Hironaka.NonmonomialOrderCanonical Hironaka.NonmonomialOrderTail
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### A phase is absorbing -/

section Absorb

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The phase is absorbing**: if `ν ≤ o` on the cosupport at the last stage of `T₀`, then along every canonical test
extension `T₀ S` every point of the cosupport lies over the cosupport at `T₀`, with `ν ≤ ν(image) ≤ o`. -/
theorem nmOrd_le_append_of_le (hn : 0 < n) (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f) {o : ℕ} {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (h0 : ∀ y ∈ (geoTransformAlong 𝔪 T₀).cosupp, nmOrd (geoTransformAlong 𝔪 T₀) y ≤ o)
    {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y) (hT : IsGeoTestTower 𝔪 (T₀.append S))
    (hcan : IsCanonical 𝔪 f (T₀.append S)) {z : Y} (hz : z ∈ (geoTransformAlong 𝔪 (T₀.append S)).cosupp) :
    S.proj z ∈ (geoTransformAlong 𝔪 T₀).cosupp ∧
      nmOrd (geoTransformAlong 𝔪 (T₀.append S)) z ≤ nmOrd (geoTransformAlong 𝔪 T₀) (S.proj z) ∧
      nmOrd (geoTransformAlong 𝔪 (T₀.append S)) z ≤ o := by
  obtain ⟨h1, h2⟩ := nmOrd_le_nmOrd_proj hn h hf T₀ S hT hcan z hz
  exact ⟨h1, h2, h2.trans (h0 _ h1)⟩

/-- **In a phase a point of order `o` lies over a point of order `o`.** -/
theorem nmOrd_proj_eq_of_le (hn : 0 < n) (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f) {o : ℕ} {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (h0 : ∀ y ∈ (geoTransformAlong 𝔪 T₀).cosupp, nmOrd (geoTransformAlong 𝔪 T₀) y ≤ o)
    {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y) (hT : IsGeoTestTower 𝔪 (T₀.append S))
    (hcan : IsCanonical 𝔪 f (T₀.append S)) {z : Y} (hz : z ∈ (geoTransformAlong 𝔪 (T₀.append S)).cosupp)
    (hzo : nmOrd (geoTransformAlong 𝔪 (T₀.append S)) z = o) :
    S.proj z ∈ (geoTransformAlong 𝔪 T₀).cosupp ∧ nmOrd (geoTransformAlong 𝔪 T₀) (S.proj z) = o := by
  obtain ⟨h1, h2, -⟩ := nmOrd_le_append_of_le hn h hf T₀ h0 S hT hcan hz
  exact ⟨h1, le_antisymm (h0 _ h1) (hzo ▸ h2)⟩

/-- **In a phase the run of a point of order `o` started at or before `T₀`**: it is in the regime `OrdRegime 𝔪 o`, and its run
is at least the length of `S`. -/
theorem ordRegime_and_length_le_regimeRun_of_le (hn : 0 < n) (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f) {o : ℕ}
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (h0 : ∀ y ∈ (geoTransformAlong 𝔪 T₀).cosupp, nmOrd (geoTransformAlong 𝔪 T₀) y ≤ o) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y), IsGeoTestTower 𝔪 (T₀.append S) → IsCanonical 𝔪 f (T₀.append S) →
      ∀ z ∈ (geoTransformAlong 𝔪 (T₀.append S)).cosupp, nmOrd (geoTransformAlong 𝔪 (T₀.append S)) z = o →
        OrdRegime 𝔪 o (T₀.append S) z ∧ S.length ≤ regimeRun (OrdRegime 𝔪 o) (T₀.append S) z
  | _, .refl, _, _, z, hz, hzo => ⟨⟨hz, hzo⟩, Nat.zero_le _⟩
  | _, .step S C π hπ, hT, hcan, z, hz, hzo => by
      have hT' : IsGeoTestTower 𝔪 (.step (T₀.append S) C π hπ) := hT
      have hcan' : IsCanonical 𝔪 f (.step (T₀.append S) C π hπ) := hcan
      obtain ⟨hπz, hle⟩ := nmOrd_step_le_of_canonical hn h hf (T₀.append S) C π hπ hT' hcan'.2 hz
      have hπo : nmOrd (geoTransformAlong 𝔪 (T₀.append S)) (π z) = o :=
        le_antisymm (nmOrd_le_append_of_le hn h hf T₀ h0 S hT'.1 hcan'.1 hπz).2.2 (hzo ▸ hle)
      obtain ⟨hreg, hrun⟩ := ordRegime_and_length_le_regimeRun_of_le hn h hf T₀ h0 S hT'.1 hcan'.1 (π z) hπz hπo
      refine ⟨⟨hz, hzo⟩, ?_⟩
      rw [BlowupTower.length_step, BlowupTower.append_step, regimeRun_step_of (OrdRegime 𝔪 o) _ C π hπ hreg]
      exact Nat.succ_le_succ hrun

/-- **In a phase the cosupport lies in the mask** `ordMask 𝔪_{T₀} o` (the open set `{ν ≤ o}` on which the companion ideal of
order `o` is formed), for `T₀` a multiple test blow-up. -/
theorem cosupp_subset_ordMask_of_le (hn : 0 < n) (h : IsInvDomain k 𝔪) {o : ℕ} {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower 𝔪 T₀)
    (h0 : ∀ y ∈ (geoTransformAlong 𝔪 T₀).cosupp, nmOrd (geoTransformAlong 𝔪 T₀) y ≤ o) :
    (geoTransformAlong 𝔪 T₀).cosupp ⊆ ordMask (geoTransformAlong 𝔪 T₀) o := by
  have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  intro y hy
  rw [SetLike.mem_coe, mem_ordMask_iff hn hdom.isWellFormed hdom.isNonzeroAlongAt]
  intro hmem
  have := (mem_ordGe_iff hdom.isWellFormed hdom.isNonzeroAlongAt (ordGe_subset_N _ _ hmem) (o + 1)).mp hmem
  have := h0 y hy
  omega

end Absorb

/-! ### The orders of the nonempty centres -/

section Centres

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Phase entry**: a point of a nonempty centre of a canonical step bounds the order on the cosupport before the step. -/
theorem nmOrd_le_of_mem_centre (hf : OrdMonotone 𝔪 f) {Y Z : CMfd.{u} n} {T : BlowupTower X Y} {C : Set Y}
    {π : Z → Y} {hπ : IsBlowupAlong n C π} (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 f (.step T C π hπ))
    {c : Y} (hc : c ∈ C) {y : Y} (hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) :
    nmOrd (geoTransformAlong 𝔪 T) y ≤ nmOrd (geoTransformAlong 𝔪 T) c := by
  have hC : C = ∅ ∨ C = maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp := hcan.2
  rcases hC with rfl | rfl
  · exact absurd hc (notMem_empty c)
  · exact nmOrd_le_of_mem_maxLocus hf hT hc hy

/-- **The orders of the nonempty centres of a canonical test segment never increase**, and every point of the last cosupport
has order at most each of them (`StepOnePhase.centreValues` of `ν`). -/
theorem pairwise_centreValues_nmOrd (hn : 0 < n) (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → IsCanonical 𝔪 f T →
      (centreValues (fun {W} (T' : BlowupTower X W) y => nmOrd (geoTransformAlong 𝔪 T') y) T).Pairwise
          (fun a b => b ≤ a) ∧
        ∀ a ∈ centreValues (fun {W} (T' : BlowupTower X W) y => nmOrd (geoTransformAlong 𝔪 T') y) T,
          ∀ z ∈ (geoTransformAlong 𝔪 T).cosupp, nmOrd (geoTransformAlong 𝔪 T) z ≤ a
  | _, .refl, _, _ => ⟨List.Pairwise.nil, fun a ha => by simp at ha⟩
  | _, .step T C π hπ, hT, hcan => by
      obtain ⟨hTT, hCadm⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      have hcanT : IsCanonical 𝔪 f T := hcan.1
      have ih := pairwise_centreValues_nmOrd hn h hf T hTT hcanT
      have hstep : ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
          π z ∈ (geoTransformAlong 𝔪 T).cosupp ∧
            nmOrd (geoTransformAlong 𝔪 (.step T C π hπ)) z ≤ nmOrd (geoTransformAlong 𝔪 T) (π z) :=
        fun z hz => nmOrd_step_le_of_canonical hn h hf T C π hπ hT hcan.2 hz
      have hold : ∀ a ∈ centreValues (fun {W} (T' : BlowupTower X W) y => nmOrd (geoTransformAlong 𝔪 T') y) T,
          ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp, nmOrd (geoTransformAlong 𝔪 (.step T C π hπ)) z ≤ a :=
        fun a ha z hz => (hstep z hz).2.trans (ih.2 a ha _ (hstep z hz).1)
      by_cases hne : C.Nonempty
      · rw [centreValues_step_of_nonempty _ T C π hπ hne]
        refine ⟨List.pairwise_append.mpr ⟨ih.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩, ?_⟩
        · rw [List.mem_singleton] at hb
          rw [hb]
          exact ih.2 a ha _ (hCadm.2.1 hne.some_mem)
        · intro a ha z hz
          rcases List.mem_append.mp ha with ha | ha
          · exact hold a ha z hz
          · rw [List.mem_singleton] at ha
            rw [ha]
            exact (hstep z hz).2.trans (nmOrd_le_of_mem_centre hf hTT hcan hne.some_mem (hstep z hz).1)
      · rw [centreValues_step_of_eq_empty _ T C π hπ (not_nonempty_iff_eq_empty.mp hne)]
        exact ⟨ih.1, hold⟩

/-- **One bound over a compact set for the orders of the centres**: for compact `K ⊆ X` there is `q` such that along every
canonical test segment, every point of a nonempty centre meeting the preimage of `K` has order `≤ q` (the centre is the maximum
locus, which lies in one level set of `ν` and meets the cosupport over `K`,
`NonmonomialOrderPhase.exists_nmOrd_le_of_isCompact_of_canonical`). -/
theorem exists_centre_nmOrd_le_of_isCompact (hn : 0 < n) (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f) {K : Set X}
    (hK : IsCompact K) :
    ∃ q : ℕ, ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower 𝔪 (.step T C π hπ) → IsCanonical 𝔪 f (.step T C π hπ) → (C ∩ T.proj ⁻¹' K).Nonempty →
        ∀ c ∈ C, nmOrd (geoTransformAlong 𝔪 T) c ≤ q := by
  obtain ⟨q, hq⟩ := NonmonomialOrderPhase.exists_nmOrd_le_of_isCompact_of_canonical hn h hf hK
  refine ⟨q, fun T C π hπ hT hcan hCK c hc => ?_⟩
  obtain ⟨hTT, hCadm⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
  have hcanT : IsCanonical 𝔪 f T := hcan.1
  obtain ⟨c₀, hc₀C, hc₀K⟩ := hCK
  have hC : C = maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp :=
    (hcan.2 : C = ∅ ∨ C = maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨c₀, hc₀C⟩)
  have hc' : c ∈ maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp := hC ▸ hc
  have hc₀' : c₀ ∈ maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp := hC ▸ hc₀C
  rw [nmOrd_eq_of_mem_maxLocus hf hTT hc₀' hc']
  exact hq T hTT hcanT c₀ (hCadm.2.1 hc₀C) hc₀K

end Centres

/-! ### The monomial phase of the general value; well-founded values -/

section Monomial

variable {Λ : Type v} [LinearOrder Λ]

/-- **A value of order `0` of the general value is `(0, inl γ)`.** -/
theorem genInv_snd_of_fst_eq_zero
    (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) {X : CMfd.{u} n}
    (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y}
    (h0 : (ofLex (GeneralValue.genInv M 𝔪 T y)).1 = 0) :
    GeneralValue.genInv M 𝔪 T y =
      toLex ((0 : ℕ), (toLex (Sum.inl (towerInvAlong 𝔪 T y)) : WithBot Val ⊕ₗ WithTop Λ)) :=
  GeneralValueOrderZero.genInv_eq_towerInvAlong M 𝔪 T h0

/-- **The monomial phase cannot go on forever**: no sequence of values `(0, inl γ_i)` of the general value's type strictly
decreases at every step (`γ`'s values are well-founded, `MonomialInvariant.wellFoundedLT_val`). -/
theorem not_strictAnti_zero_inl (g : ℕ → WithBot Val) :
    ¬ StrictAnti (fun i => (toLex ((0 : ℕ), (toLex (Sum.inl (g i)) : WithBot Val ⊕ₗ WithTop Λ)) :
      ℕ ×ₗ (WithBot Val ⊕ₗ WithTop Λ))) := by
  intro hanti
  have : WellFoundedLT (WithBot Val) := wellFoundedLT_val
  refine not_strictAnti_of_wellFoundedLT g fun i j hij => ?_
  have h := hanti hij
  rw [Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨-, h⟩
  · exact absurd h (lt_irrefl 0)
  · exact Sum.Lex.inl_lt_inl_iff.mp h

/-- **The values of the general step are well-founded when those of the maximal-order value are.** -/
theorem wellFoundedLT_genValue [WellFoundedLT Λ] : WellFoundedLT (ℕ ×ₗ (WithBot Val ⊕ₗ WithTop Λ)) := by
  have h1 : WellFoundedLT (WithBot Val) := wellFoundedLT_val
  have h2 : WellFoundedLT (WithTop Λ) := inferInstance
  have : WellFoundedLT (WithBot Val ⊕ₗ WithTop Λ) := ⟨Sum.lex_wf h1.wf h2.wf⟩
  infer_instance

end Monomial

end

end Hironaka.NonmonomialOrderGlobalPhase
