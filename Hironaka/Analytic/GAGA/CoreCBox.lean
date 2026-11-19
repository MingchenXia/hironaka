import Hironaka.Analytic.GAGA.CoreCousin

/-!
# Compact convex product sets: cuts, degree and bisection

Infrastructure of lane SERRE-CORE3 (Serre's GAGA, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), step M2.4--M2.5 of the plan in
`blueprint/src/claude-serre-core.tex` (see `blueprint/src/claude-serre-core3.tex`).

A *box* is a family `C : Fin n → Set ℂ` of compact convex sets; its product set is
`boxSet C = {z ∈ ℂⁿ : z_l ∈ C_l ∀ l}` (closed polydiscs, closed cubes and their faces are of this
form). The real directions of a factor are `Re w = Re(1 · w)` and `Im w = Re(-i · w)` (`dirC`).

* `cut C i θ S`: replace `C_i` by `C_i ∩ {Re(θ w) ∈ S}`; with `S = Iic t`, `Ici t`, `{t}` these
  are the two halves and the face of the splitting of `boxSet C` by the real hyperplane
  `Re(θ z_i) = t` (`mem_boxSet_cut`).
* `nonconstDirs C`, `boxDeg C`: the directions `(l, d)` along which `C_l` is not constant, and
  their number (the *degree*). A face has smaller degree (`boxDeg_face_lt`), sub-boxes have no
  larger degree, and when the cut direction is constant one half is the whole box
  (`cut_Iic_or_Ici_eq_self`).
* `bisection`: a property of sub-boxes which holds for empty and for small boxes (near every
  point) and passes from the two halves of a cut to the whole holds for the box (Lebesgue
  number and slicing in each of the `2n` real directions).
-/

set_option autoImplicit false

open Set Filter Metric Complex
open scoped Topology

namespace Hironaka.Analytic.GAGA.Core.Box

variable {n : ℕ}

/-! ### Product sets and cuts -/

/-- The product set `∏ C_l ⊆ ℂⁿ`. -/
def boxSet (C : Fin n → Set ℂ) : Set (EuclideanSpace ℂ (Fin n)) :=
  {z | ∀ l, z l ∈ C l}

theorem mem_boxSet {C : Fin n → Set ℂ} {z : EuclideanSpace ℂ (Fin n)} :
    z ∈ boxSet C ↔ ∀ l, z l ∈ C l :=
  Iff.rfl

theorem boxSet_mono {C C' : Fin n → Set ℂ} (h : C' ≤ C) : boxSet C' ⊆ boxSet C :=
  fun _ hz l => h l (hz l)

/-- `C` is a family of compact convex subsets of `ℂ` (a *box*). -/
structure IsBox (C : Fin n → Set ℂ) : Prop where
  isCompact : ∀ l, IsCompact (C l)
  convex : ∀ l, Convex ℝ (C l)

theorem IsBox.isCompact_boxSet {C : Fin n → Set ℂ} (hC : IsBox C) : IsCompact (boxSet C) :=
  Cousin.isCompact_coord_pi hC.isCompact

/-- The real direction `d` of `ℂ`: `Re(dirC 0 · w) = Re w`, `Re(dirC 1 · w) = Im w`. -/
def dirC (d : Fin 2) : ℂ :=
  if d = 0 then 1 else -I

theorem continuous_lin (θ : ℂ) : Continuous fun w : ℂ => (θ * w).re :=
  continuous_re.comp (continuous_const.mul continuous_id)

theorem isLinearMap_lin (θ : ℂ) : IsLinearMap ℝ fun w : ℂ => (θ * w).re := by
  refine ⟨fun x y => by simp [mul_add], fun c x => ?_⟩
  simp only [Complex.real_smul, smul_eq_mul]
  rw [mul_left_comm, Complex.re_ofReal_mul]

/-- Cut of the `i`-th factor by the condition `Re(θ w) ∈ S`. -/
def cut (C : Fin n → Set ℂ) (i : Fin n) (θ : ℂ) (S : Set ℝ) : Fin n → Set ℂ :=
  Function.update C i (C i ∩ {w | (θ * w).re ∈ S})

theorem cut_apply_self (C : Fin n → Set ℂ) (i : Fin n) (θ : ℂ) (S : Set ℝ) :
    cut C i θ S i = C i ∩ {w | (θ * w).re ∈ S} := by
  simp [cut]

theorem cut_apply_of_ne (C : Fin n → Set ℂ) {i l : Fin n} (θ : ℂ) (S : Set ℝ) (h : l ≠ i) :
    cut C i θ S l = C l := by
  simp [cut, Function.update_of_ne h]

theorem mem_boxSet_cut {C : Fin n → Set ℂ} {i : Fin n} {θ : ℂ} {S : Set ℝ}
    {z : EuclideanSpace ℂ (Fin n)} :
    z ∈ boxSet (cut C i θ S) ↔ z ∈ boxSet C ∧ (θ * z i).re ∈ S := by
  constructor
  · intro h
    have hi := h i
    rw [cut_apply_self] at hi
    refine ⟨fun l => ?_, hi.2⟩
    by_cases hl : l = i
    · subst hl; exact hi.1
    · have := h l
      rwa [cut_apply_of_ne C θ S hl] at this
  · rintro ⟨h, hS⟩ l
    by_cases hl : l = i
    · subst hl; rw [cut_apply_self]; exact ⟨h l, hS⟩
    · rw [cut_apply_of_ne C θ S hl]; exact h l

theorem boxSet_cut_Iic (C : Fin n → Set ℂ) (i : Fin n) (θ : ℂ) (t : ℝ) :
    boxSet (cut C i θ (Iic t)) = {z | (∀ l, z l ∈ C l) ∧ (θ * z i).re ≤ t} := by
  ext z; exact mem_boxSet_cut

theorem boxSet_cut_Ici (C : Fin n → Set ℂ) (i : Fin n) (θ : ℂ) (t : ℝ) :
    boxSet (cut C i θ (Ici t)) = {z | (∀ l, z l ∈ C l) ∧ t ≤ (θ * z i).re} := by
  ext z; exact mem_boxSet_cut

theorem boxSet_cut_singleton (C : Fin n → Set ℂ) (i : Fin n) (θ : ℂ) (t : ℝ) :
    boxSet (cut C i θ {t}) = {z | (∀ l, z l ∈ C l) ∧ (θ * z i).re = t} := by
  ext z; exact mem_boxSet_cut

theorem cut_le (C : Fin n → Set ℂ) (i : Fin n) (θ : ℂ) (S : Set ℝ) : cut C i θ S ≤ C := by
  intro l
  by_cases hl : l = i
  · subst hl; rw [cut_apply_self]; exact inter_subset_left
  · rw [cut_apply_of_ne C θ S hl]

theorem cut_mono_set (C : Fin n → Set ℂ) (i : Fin n) (θ : ℂ) {S S' : Set ℝ} (h : S ⊆ S') :
    cut C i θ S ≤ cut C i θ S' := by
  intro l
  by_cases hl : l = i
  · subst hl; rw [cut_apply_self, cut_apply_self]
    exact fun w hw => ⟨hw.1, h hw.2⟩
  · rw [cut_apply_of_ne C θ S hl, cut_apply_of_ne C θ S' hl]

theorem cut_cut (C : Fin n → Set ℂ) (i : Fin n) (θ : ℂ) (S S' : Set ℝ) :
    cut (cut C i θ S) i θ S' = cut C i θ (S ∩ S') := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp only [cut_apply_self]
    ext w
    simp [and_assoc]
  · rw [cut_apply_of_ne _ θ _ hl, cut_apply_of_ne _ θ _ hl, cut_apply_of_ne _ θ _ hl]

theorem cut_eq_self {C : Fin n → Set ℂ} {i : Fin n} {θ : ℂ} {S : Set ℝ}
    (h : ∀ w ∈ C i, (θ * w).re ∈ S) : cut C i θ S = C := by
  unfold cut
  rw [Function.update_eq_self_iff]
  exact inter_eq_left.2 h

theorem IsBox.cut_of_closed {C : Fin n → Set ℂ} (hC : IsBox C) (i : Fin n) (θ : ℂ) {S : Set ℝ}
    (hSc : IsClosed S) (hSv : Convex ℝ S) : IsBox (cut C i θ S) := by
  refine ⟨fun l => ?_, fun l => ?_⟩
  · by_cases hl : l = i
    · subst hl; rw [cut_apply_self]
      exact (hC.isCompact l).inter_right (hSc.preimage (continuous_lin θ))
    · rw [cut_apply_of_ne C θ S hl]; exact hC.isCompact l
  · by_cases hl : l = i
    · subst hl; rw [cut_apply_self]
      exact (hC.convex l).inter (hSv.is_linear_preimage (isLinearMap_lin θ))
    · rw [cut_apply_of_ne C θ S hl]; exact hC.convex l

theorem IsBox.cut_Iic {C : Fin n → Set ℂ} (hC : IsBox C) (i : Fin n) (θ : ℂ) (t : ℝ) :
    IsBox (cut C i θ (Iic t)) :=
  hC.cut_of_closed i θ isClosed_Iic (convex_Iic t)

theorem IsBox.cut_Ici {C : Fin n → Set ℂ} (hC : IsBox C) (i : Fin n) (θ : ℂ) (t : ℝ) :
    IsBox (cut C i θ (Ici t)) :=
  hC.cut_of_closed i θ isClosed_Ici (convex_Ici t)

theorem IsBox.cut_singleton {C : Fin n → Set ℂ} (hC : IsBox C) (i : Fin n) (θ : ℂ) (t : ℝ) :
    IsBox (cut C i θ {t}) :=
  hC.cut_of_closed i θ isClosed_singleton (convex_singleton t)

theorem IsBox.cut_Icc {C : Fin n → Set ℂ} (hC : IsBox C) (i : Fin n) (θ : ℂ) (s t : ℝ) :
    IsBox (cut C i θ (Icc s t)) :=
  hC.cut_of_closed i θ isClosed_Icc (convex_Icc s t)

/-! ### Degree -/

/-- The real direction `p = (l, d)` is constant on the factor `C_l`. -/
def ConstDir (C : Fin n → Set ℂ) (p : Fin n × Fin 2) : Prop :=
  ∀ w ∈ C p.1, ∀ w' ∈ C p.1, (dirC p.2 * w).re = (dirC p.2 * w').re

open Classical in
/-- The real directions along which the box is not constant. -/
noncomputable def nonconstDirs (C : Fin n → Set ℂ) : Finset (Fin n × Fin 2) :=
  Finset.univ.filter fun p => ¬ ConstDir C p

/-- The **degree** of a box: the number of non-constant real projections `Re z_l`, `Im z_l`. -/
noncomputable def boxDeg (C : Fin n → Set ℂ) : ℕ :=
  (nonconstDirs C).card

theorem mem_nonconstDirs {C : Fin n → Set ℂ} {p : Fin n × Fin 2} :
    p ∈ nonconstDirs C ↔ ¬ ConstDir C p := by
  simp [nonconstDirs]

theorem ConstDir.mono {C C' : Fin n → Set ℂ} (h : C' ≤ C) {p : Fin n × Fin 2}
    (hp : ConstDir C p) : ConstDir C' p :=
  fun w hw w' hw' => hp w (h p.1 hw) w' (h p.1 hw')

theorem nonconstDirs_mono {C C' : Fin n → Set ℂ} (h : C' ≤ C) :
    nonconstDirs C' ⊆ nonconstDirs C := by
  intro p hp
  rw [mem_nonconstDirs] at hp ⊢
  exact fun hc => hp (hc.mono h)

theorem boxDeg_mono {C C' : Fin n → Set ℂ} (h : C' ≤ C) : boxDeg C' ≤ boxDeg C :=
  Finset.card_le_card (nonconstDirs_mono h)

/-- The face of a cut is constant in the cut direction. -/
theorem nonconstDirs_face_subset (C : Fin n → Set ℂ) (i : Fin n) (d : Fin 2) (t : ℝ) :
    nonconstDirs (cut C i (dirC d) {t}) ⊆ (nonconstDirs C).erase (i, d) := by
  intro p hp
  rw [Finset.mem_erase]
  refine ⟨fun hpe => ?_, nonconstDirs_mono (cut_le C i _ _) hp⟩
  subst hpe
  rw [mem_nonconstDirs] at hp
  apply hp
  show ∀ w ∈ cut C i (dirC d) {t} i, ∀ w' ∈ cut C i (dirC d) {t} i,
    (dirC d * w).re = (dirC d * w').re
  rw [cut_apply_self]
  intro w hw w' hw'
  exact (mem_singleton_iff.1 hw.2).trans (mem_singleton_iff.1 hw'.2).symm

/-- **The degree drops on the face** of a cut in a non-constant direction. -/
theorem boxDeg_face_lt {C : Fin n → Set ℂ} {i : Fin n} {d : Fin 2} (hp : (i, d) ∈ nonconstDirs C)
    (t : ℝ) : boxDeg (cut C i (dirC d) {t}) < boxDeg C := by
  unfold boxDeg
  calc (nonconstDirs (cut C i (dirC d) {t})).card ≤ ((nonconstDirs C).erase (i, d)).card :=
        Finset.card_le_card (nonconstDirs_face_subset C i d t)
    _ < (nonconstDirs C).card := Finset.card_erase_lt_of_mem hp

/-- In a constant direction one of the two halves of a cut is the whole box. -/
theorem cut_Iic_or_Ici_eq_self {C : Fin n → Set ℂ} {i : Fin n} {d : Fin 2}
    (hc : ConstDir C (i, d)) (t : ℝ) :
    cut C i (dirC d) (Iic t) = C ∨ cut C i (dirC d) (Ici t) = C := by
  by_cases h : ∀ w ∈ C i, (dirC d * w).re ≤ t
  · exact Or.inl (cut_eq_self h)
  · simp only [not_forall, not_le, exists_prop] at h
    obtain ⟨w₀, hw₀, ht⟩ := h
    refine Or.inr (cut_eq_self fun w hw => ?_)
    have : (dirC d * w).re = (dirC d * w₀).re := hc w hw w₀ hw₀
    rw [mem_Ici, this]
    exact ht.le

/-! ### Bisection -/

theorem norm_le_sum_norm (v : EuclideanSpace ℂ (Fin n)) : ‖v‖ ≤ ∑ l, ‖v l‖ := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ l, ‖v l‖ ^ 2) ≤ √((∑ l, ‖v l‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun l _ => norm_nonneg _)
    _ = ∑ l, ‖v l‖ := Real.sqrt_sq (Finset.sum_nonneg fun l _ => norm_nonneg _)

theorem dirC_zero_mul_re (w : ℂ) : (dirC 0 * w).re = w.re := by
  simp [dirC]

theorem dirC_one_mul_re (w : ℂ) : (dirC 1 * w).re = w.im := by
  simp [dirC]

/-- `B` has width at most `η` in the direction `p`. -/
def Narrow (η : ℝ) (B : Fin n → Set ℂ) (p : Fin n × Fin 2) : Prop :=
  ∀ w ∈ B p.1, ∀ w' ∈ B p.1, |(dirC p.2 * w).re - (dirC p.2 * w').re| ≤ η

theorem Narrow.mono {η : ℝ} {B B' : Fin n → Set ℂ} (h : B' ≤ B) {p : Fin n × Fin 2}
    (hp : Narrow η B p) : Narrow η B' p :=
  fun w hw w' hw' => hp w (h p.1 hw) w' (h p.1 hw')

/-- Points of a box narrow in every direction are close. -/
theorem norm_sub_le_of_narrow {η : ℝ} {B : Fin n → Set ℂ} (hB : ∀ p, Narrow η B p)
    {z x : EuclideanSpace ℂ (Fin n)} (hz : z ∈ boxSet B) (hx : x ∈ boxSet B) :
    ‖z - x‖ ≤ 2 * n * η := by
  have hl : ∀ l, ‖(z - x) l‖ ≤ 2 * η := by
    intro l
    have h0 := hB (l, 0) (z l) (hz l) (x l) (hx l)
    have h1 := hB (l, 1) (z l) (hz l) (x l) (hx l)
    simp only [dirC_zero_mul_re, dirC_one_mul_re] at h0 h1
    have : ‖(z - x) l‖ ≤ |((z - x) l).re| + |((z - x) l).im| := by
      simpa using Complex.norm_le_abs_re_add_abs_im ((z - x) l)
    have hre : ((z - x) l).re = (z l).re - (x l).re := by simp
    have him : ((z - x) l).im = (z l).im - (x l).im := by simp
    rw [hre, him] at this
    linarith
  calc ‖z - x‖ ≤ ∑ l, ‖(z - x) l‖ := norm_le_sum_norm _
    _ ≤ ∑ _l : Fin n, 2 * η := Finset.sum_le_sum fun l _ => hl l
    _ = 2 * n * η := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Bisection.** Let `C` be a box and `P` a property of boxes. Suppose that `P` holds for every
empty sub-box, that every point `x` of `boxSet C` has a neighbourhood `N` such that `P` holds for
every sub-box whose product set lies in `N`, and that `P` passes from the two halves of every cut
`Re(θ z_i) ≤ t`, `Re(θ z_i) ≥ t` (`θ = 1, -i`) of a sub-box to the sub-box. Then `P C`. -/
theorem bisection {C : Fin n → Set ℂ} (hC : IsBox C) (P : (Fin n → Set ℂ) → Prop)
    (hempty : ∀ B ≤ C, IsBox B → boxSet B = ∅ → P B)
    (hloc : ∀ x ∈ boxSet C, ∃ N ∈ 𝓝 x, ∀ B ≤ C, IsBox B → boxSet B ⊆ N → P B)
    (hmerge : ∀ B ≤ C, IsBox B → ∀ (i : Fin n) (d : Fin 2) (t : ℝ),
      P (cut B i (dirC d) (Iic t)) → P (cut B i (dirC d) (Ici t)) → P B) :
    P C := by
  classical
  choose N hN hNP using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hC.isCompact_boxSet
    (c := fun x : boxSet C => interior (N x x.2)) (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hN x hx)⟩)
  set η : ℝ := δ / (2 * n + 1) with hη
  have hηpos : 0 < η := div_pos hδ (by positivity)
  have hsmall : 2 * n * η < δ := by
    rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- small boxes
  have hbase : ∀ B ≤ C, IsBox B → (∀ p, Narrow η B p) → P B := by
    intro B hBC hB hnar
    rcases (boxSet B).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · exact hempty B hBC hB he
    · obtain ⟨y, hy⟩ := hleb x (boxSet_mono hBC hx)
      refine hNP y y.2 B hBC hB fun z hz => interior_subset (hy ?_)
      rw [mem_ball, dist_eq_norm]
      exact (norm_sub_le_of_narrow hnar hz hx).trans_lt hsmall
  -- slicing direction by direction
  have hclaim : ∀ F : Finset (Fin n × Fin 2), ∀ B ≤ C, IsBox B → (∀ p ∉ F, Narrow η B p) →
      P B := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact fun B hBC hB hnar => hbase B hBC hB fun p => hnar p (by simp)
    | insert p F hpF ih =>
      intro B hBC hB hnar
      obtain ⟨i, d⟩ := p
      set θ := dirC d with hθ
      obtain ⟨a, ha⟩ := (hB.isCompact i).bddBelow_image (continuous_lin θ).continuousOn
      obtain ⟨b, hb⟩ := (hB.isCompact i).bddAbove_image (continuous_lin θ).continuousOn
      have ha' : ∀ w ∈ B i, a ≤ (θ * w).re := fun w hw => ha ⟨w, hw, rfl⟩
      have hb' : ∀ w ∈ B i, (θ * w).re ≤ b := fun w hw => hb ⟨w, hw, rfl⟩
      -- a sub-box of `B`, narrow in the direction `(i, d)`, satisfies `P`
      have hsub : ∀ S : Set ℝ, IsBox (cut B i θ S) →
          (∀ w ∈ B i, ∀ w' ∈ B i, (θ * w).re ∈ S → (θ * w').re ∈ S →
            |(θ * w).re - (θ * w').re| ≤ η) → P (cut B i θ S) := by
        intro S hS hSn
        refine ih _ ((cut_le B i θ S).trans hBC) hS fun q hq => ?_
        by_cases hqp : q = (i, d)
        · subst hqp
          show ∀ w ∈ cut B i θ S i, ∀ w' ∈ cut B i θ S i,
            |(θ * w).re - (θ * w').re| ≤ η
          rw [cut_apply_self]
          intro w hw w' hw'
          exact hSn w hw.1 w' hw'.1 hw.2 hw'.2
        · exact (hnar q (by simp [hqp, hq])).mono (cut_le B i θ S)
      have hstep : ∀ k : ℕ, P (cut B i θ (Iic (a + k * η))) := by
        intro k
        induction k with
        | zero =>
          refine hsub _ (hB.cut_Iic i θ _) fun w hw w' hw' h h' => ?_
          simp only [Nat.cast_zero, zero_mul, add_zero, mem_Iic] at h h'
          have e1 := le_antisymm h (ha' w hw)
          have e2 := le_antisymm h' (ha' w' hw')
          rw [e1, e2, sub_self, abs_zero]
          exact hηpos.le
        | succ k ihk =>
          have hB' : IsBox (cut B i θ (Iic (a + ((k + 1 : ℕ) : ℝ) * η))) := hB.cut_Iic i θ _
          have hle := hmerge _ ((cut_le B i θ _).trans hBC) hB' i d (a + k * η)
          rw [← hθ, cut_cut, cut_cut] at hle
          have e1 : Iic (a + ((k + 1 : ℕ) : ℝ) * η) ∩ Iic (a + k * η) = Iic (a + k * η) := by
            rw [Iic_inter_Iic, inf_eq_right.2 (by push_cast; nlinarith)]
          have e2 : Iic (a + ((k + 1 : ℕ) : ℝ) * η) ∩ Ici (a + k * η) =
              Icc (a + k * η) (a + k * η + η) := by
            rw [Iic_inter_Ici]; congr 1; push_cast; ring
          rw [e1, e2] at hle
          refine hle ihk (hsub _ (hB.cut_Icc i θ _ _) fun w hw w' hw' h h' => ?_)
          rw [abs_le]
          constructor <;> linarith [h.1, h.2, h'.1, h'.2]
      obtain ⟨k, hk⟩ := exists_nat_ge ((b - a) / η)
      have hkb : b ≤ a + k * η := by
        rw [div_le_iff₀ hηpos] at hk; linarith
      have hcut : cut B i θ (Iic (a + k * η)) = B :=
        cut_eq_self fun w hw => (hb' w hw).trans hkb
      have := hstep k
      rwa [hcut] at this
  exact hclaim Finset.univ C le_rfl hC fun p hp => absurd (Finset.mem_univ p) hp

end Hironaka.Analytic.GAGA.Core.Box
