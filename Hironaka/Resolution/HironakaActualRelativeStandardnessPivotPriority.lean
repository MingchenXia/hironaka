import Hironaka.Resolution.HironakaActualCanonicalDirectionPivot
import Hironaka.Resolution.HironakaActualPointChartTransition
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Stable promotion of a cylindrical pivot to coordinate zero

The relative order of all other coordinates is preserved. A cylindrical source
diagram, rather than arbitrary coordinate covariance of degree-lex order, makes
the SAME canonical members and their permuted actual vertex labels persist.
This is a genuine formal coordinate dictionary, not an unchanged-HS phase.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualRelativeStandardnessPivotPriority

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalStandardMonomialHS HironakaActualPointChartTransition

variable {n : ℕ}

/-- Stable old-to-new relabelling: the pivot goes first and all other coordinates
remain in their old relative order. This is not a transposition. -/
def pivotFirstEquiv (f : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) :=
  (finSuccEquiv' f).trans (finSuccEquiv n).symm

private theorem pivotFirstEquiv_pivot (f : Fin (n + 1)) : pivotFirstEquiv f f = 0 := by
  simp only [pivotFirstEquiv, Equiv.trans_apply, finSuccEquiv'_at, finSuccEquiv_symm_none]

private theorem pivotFirstEquiv_succAbove (f : Fin (n + 1)) (i : Fin n) :
    pivotFirstEquiv f (f.succAbove i) = i.succ := by
  simp only [pivotFirstEquiv, Equiv.trans_apply, finSuccEquiv'_succAbove, finSuccEquiv_symm_some]

private theorem pivotFirstEquiv_symm_zero (f : Fin (n + 1)) :
    (pivotFirstEquiv f).symm 0 = f := by
  apply (pivotFirstEquiv f).injective
  rw [Equiv.apply_symm_apply, pivotFirstEquiv_pivot]

private theorem pivotFirstEquiv_symm_succ (f : Fin (n + 1)) (i : Fin n) :
    (pivotFirstEquiv f).symm i.succ = f.succAbove i := by
  apply (pivotFirstEquiv f).injective
  rw [Equiv.apply_symm_apply, pivotFirstEquiv_succAbove]

/-- The actual additive exponent permutation of the stable coordinate relabelling. -/
def pivotFirstExponent (f : Fin (n + 1)) :
    (Fin (n + 1) →₀ ℕ) ≃+ (Fin (n + 1) →₀ ℕ) := Finsupp.domCongr (pivotFirstEquiv f)

private theorem permuteExponent_apply (p : Fin (n + 1) ≃ Fin (n + 1))
    (α : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) :
    Finsupp.domCongr p α i = α (p.symm i) := by
  simp only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_equiv_apply]

private theorem pivotFirstExponent_zero (f : Fin (n + 1)) (α : Fin (n + 1) →₀ ℕ) :
    pivotFirstExponent f α 0 = α f := by
  rw [pivotFirstExponent, permuteExponent_apply, pivotFirstEquiv_symm_zero]

private theorem pivotFirstExponent_succ (f : Fin (n + 1)) (α : Fin (n + 1) →₀ ℕ) (i : Fin n) :
    pivotFirstExponent f α i.succ = α (f.succAbove i) := by
  rw [pivotFirstExponent, permuteExponent_apply, pivotFirstEquiv_symm_succ]

private theorem permuteExponent_degree (p : Fin (n + 1) ≃ Fin (n + 1))
    (α : Fin (n + 1) →₀ ℕ) : Finsupp.degree (Finsupp.domCongr p α) = Finsupp.degree α := by
  simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain] using
    Finsupp.degree_mapDomain p α

private theorem pivotFirstExponent_degree (f : Fin (n + 1)) (α : Fin (n + 1) →₀ ℕ) :
    normalExponentDegree (pivotFirstExponent f α) = normalExponentDegree α := by
  simpa only [pivotFirstExponent, normalExponentDegree, ← Finsupp.degree_eq_sum] using
    permuteExponent_degree (pivotFirstEquiv f) α

private theorem permuteExponent_le_iff (p : Fin (n + 1) ≃ Fin (n + 1))
    (α β : Fin (n + 1) →₀ ℕ) : Finsupp.domCongr p α ≤ Finsupp.domCongr p β ↔ α ≤ β := by
  constructor
  · intro h i
    have hi := h (p i)
    simpa only [permuteExponent_apply, Equiv.symm_apply_apply] using hi
  · intro h i
    simp only [permuteExponent_apply]
    exact h (p.symm i)

/-- Moving a zero head-coordinate to the first lexicographic priority preserves
every strict comparison from that head, including equal total degree. -/
theorem pivotFirstExponent_strict_of_transverse_head (f : Fin (n + 1))
    (a β : Fin (n + 1) →₀ ℕ) (haf : a f = 0)
    (h : MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn β) :
    MonomialOrder.degLex.toSyn (pivotFirstExponent f a) <
      MonomialOrder.degLex.toSyn (pivotFirstExponent f β) := by
  have hd (α : Fin (n + 1) →₀ ℕ) :
      Finsupp.degree (pivotFirstExponent f α) = Finsupp.degree α :=
    permuteExponent_degree (pivotFirstEquiv f) α
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  rcases Finsupp.DegLex.lt_iff.mp (MonomialOrder.degLex_lt_iff.mp h) with hdegree | ⟨hdegree, hlex⟩
  · left
    simpa only [ofDegLex_toDegLex, hd] using hdegree
  · right
    refine ⟨by simpa only [ofDegLex_toDegLex, hd] using hdegree, ?_⟩
    apply Finsupp.Lex.lt_iff.mpr
    by_cases hβf : β f = 0
    · obtain ⟨j, hbefore, hj⟩ := Finsupp.Lex.lt_iff.mp hlex
      simp only [ofDegLex_toDegLex, ofLex_toLex] at hbefore hj
      have hjf : j ≠ f := by
        intro he
        rw [he, haf, hβf] at hj
        exact (lt_irrefl 0) hj
      obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hjf
      refine ⟨l.succ, ?_, ?_⟩
      · intro i hi
        obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ i
        · simp only [ofDegLex_toDegLex, ofLex_toLex, pivotFirstExponent_zero, haf, hβf]
        · simp only [ofDegLex_toDegLex, ofLex_toLex, pivotFirstExponent_succ]
          apply hbefore
          rw [← hl]
          exact Fin.strictMono_succAbove f (Fin.succ_lt_succ_iff.mp hi)
      · simpa only [ofDegLex_toDegLex, ofLex_toLex, pivotFirstExponent_succ, hl] using hj
    · refine ⟨0, fun i hi => False.elim ((not_lt_of_ge (Fin.zero_le i)) hi), ?_⟩
      simpa only [ofDegLex_toDegLex, ofLex_toLex, pivotFirstExponent_zero, haf] using
        Nat.pos_of_ne_zero hβf

/-- Actual whole formal coordinate renaming by the stable pivot permutation. -/
def pivotFirstRename (f : Fin (n + 1)) :
    MvPowerSeries (Fin (n + 1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (n + 1)) ℂ :=
  MvPowerSeries.rename (pivotFirstEquiv f)

private theorem coeff_rename_permuted (p : Fin (n + 1) ≃ Fin (n + 1))
    (F : MvPowerSeries (Fin (n + 1)) ℂ) (α : Fin (n + 1) →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.domCongr p α) (MvPowerSeries.rename p F) =
      MvPowerSeries.coeff α F := by
  simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding] using
    MvPowerSeries.coeff_embDomain_rename p.toEmbedding F α

/-- SAME source canonical members retain their literal renamed heads. -/
theorem pivotFirstReducedSeries_monic
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    MvPowerSeries.coeff (pivotFirstExponent f a.val)
      (pivotFirstRename f (actualReducedVertexSeries MonomialOrder.degLex K a)) = 1 ∧
      ∀ γ, MonomialOrder.degLex.toSyn γ <
          MonomialOrder.degLex.toSyn (pivotFirstExponent f a.val) →
        MvPowerSeries.coeff γ
          (pivotFirstRename f (actualReducedVertexSeries MonomialOrder.degLex K a)) = 0 := by
  constructor
  · rw [pivotFirstRename, pivotFirstExponent, coeff_rename_permuted]
    exact actualReducedVertexSeries_coefficient MonomialOrder.degLex K a
  · intro γ hγ
    let β := (pivotFirstExponent f).symm γ
    have hβγ : pivotFirstExponent f β = γ := (pivotFirstExponent f).apply_symm_apply γ
    rw [← hβγ, pivotFirstRename, pivotFirstExponent, coeff_rename_permuted]
    by_contra hcoeff
    have haβ : MonomialOrder.degLex.toSyn a.val ≤ MonomialOrder.degLex.toSyn β := by
      by_contra h
      exact hcoeff (actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex K a β
        (lt_of_not_ge h))
    rcases lt_or_eq_of_le haβ with hlt | heq
    · have hnew := pivotFirstExponent_strict_of_transverse_head f a.val β (hv a) hlt
      rw [hβγ] at hnew
      exact (not_lt_of_ge hnew.le) hγ
    · have heq' : β = a.val := (MonomialOrder.degLex.toSyn.injective heq).symm
      have hγa : γ = pivotFirstExponent f a.val :=
        hβγ.symm.trans (congrArg (pivotFirstExponent f) heq')
      rw [hγa] at hγ
      exact (lt_irrefl _) hγ

private theorem renamed_diagram_inclusion
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0) :
    (pivotFirstExponent f) '' actualInitialDiagram MonomialOrder.degLex K ⊆
      actualInitialDiagram MonomialOrder.degLex (Ideal.map (pivotFirstRename f).toRingHom K) := by
  rintro γ ⟨α, hα, rfl⟩
  obtain ⟨a, ha, hle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K α).mp hα
  let v : actualInitialVertices MonomialOrder.degLex K := ⟨a, ha⟩
  let R := pivotFirstRename f (actualReducedVertexSeries MonomialOrder.degLex K v)
  have hm := pivotFirstReducedSeries_monic K f hv v
  have hne : R ≠ 0 := by
    intro h
    have hc := hm.1
    change MvPowerSeries.coeff (pivotFirstExponent f v.val) R = 1 at hc
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  have hinitial : actualInitialExponent MonomialOrder.degLex R hne = pivotFirstExponent f a :=
    actualInitialExponent_eq_of_coefficients MonomialOrder.degLex R hne _
      (by rw [hm.1]; exact one_ne_zero) hm.2
  apply actualInitialDiagram_upper MonomialOrder.degLex _ (pivotFirstExponent f a)
    (pivotFirstExponent f α)
      ⟨R, Ideal.mem_map_of_mem _ (actualReducedVertexSeries_mem MonomialOrder.degLex K v), hne, hinitial⟩
  exact (permuteExponent_le_iff (pivotFirstEquiv f) a α).mpr hle

/-- A true permutation of variables preserves their entire formal ideal. -/
theorem map_genuineFormalVariables_rename (p : Fin (n + 1) ≃ Fin (n + 1)) :
    Ideal.map (MvPowerSeries.renameEquiv ℂ p).toRingEquiv.toRingHom
      (genuineFormalVariables (n + 1)) = genuineFormalVariables (n + 1) := by
  apply le_antisymm
  · rw [genuineFormalVariables, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro F ⟨G, ⟨i, rfl⟩, rfl⟩
    change MvPowerSeries.rename p (MvPowerSeries.X i) ∈ genuineFormalVariables (n + 1)
    rw [MvPowerSeries.rename_X]
    exact Ideal.subset_span ⟨p i, rfl⟩
  · apply Ideal.span_le.mpr
    rintro F ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := p.surjective i
    have h := Ideal.mem_map_of_mem (MvPowerSeries.renameEquiv ℂ p).toRingEquiv.toRingHom
      (Ideal.subset_span (show (MvPowerSeries.X j : MvPowerSeries (Fin (n + 1)) ℂ) ∈
        Set.range MvPowerSeries.X from ⟨j, rfl⟩))
    change MvPowerSeries.rename p (MvPowerSeries.X j) ∈ _ at h
    rwa [MvPowerSeries.rename_X] at h

/-- Whole genuine HS dimensions close the reverse diagram inclusion after the
stable promotion of an actual cylindrical pivot. -/
theorem actualInitialDiagram_pivotFirst
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0) :
    actualInitialDiagram MonomialOrder.degLex (Ideal.map (pivotFirstRename f).toRingHom K) =
      (pivotFirstExponent f) '' actualInitialDiagram MonomialOrder.degLex K := by
  have hIncl := renamed_diagram_inclusion K f hv
  apply le_antisymm ?_ hIncl
  intro γ hγ
  let E := pivotFirstExponent f
  let J := Ideal.map (pivotFirstRename f).toRingHom K
  by_contra hnot
  let α := E.symm γ
  have hα : α ∉ actualInitialDiagram MonomialOrder.degLex K := by
    intro h
    exact hnot ⟨α, h, E.apply_symm_apply γ⟩
  let q := normalExponentDegree α
  let g : actualStandardIndex (n + 1) J (q + 1) → actualStandardIndex (n + 1) K (q + 1) :=
    fun c => ⟨⟨E.symm c.val.val, by
      have hd := pivotFirstExponent_degree f (E.symm c.val.val)
      rw [E.apply_symm_apply] at hd
      rw [← hd]
      exact c.val.property⟩, by
      intro h
      have hc := hIncl ⟨E.symm c.val.val, h, E.apply_symm_apply c.val.val⟩
      exact c.property hc⟩
  have hg : Function.Injective g := by
    intro c d h
    have he := congrArg (fun a : actualStandardIndex (n + 1) K (q + 1) => E a.val.val) h
    simp only [g, E.apply_symm_apply] at he
    exact Subtype.ext (Subtype.ext he)
  have hHS : genuineFormalHilbertSamuelValue (n + 1) K q =
      genuineFormalHilbertSamuelValue (n + 1) J q :=
    genuineFormalHilbertSamuelValue_map_formalAlgEquiv
      (MvPowerSeries.renameEquiv ℂ (pivotFirstEquiv f))
        (map_genuineFormalVariables_rename (pivotFirstEquiv f)) K q
  have hcard : Fintype.card (actualStandardIndex (n + 1) J (q + 1)) =
      Fintype.card (actualStandardIndex (n + 1) K (q + 1)) := by
    rw [← genuineFormalHilbertSamuelValue_eq_card_standardIndex J q,
      ← genuineFormalHilbertSamuelValue_eq_card_standardIndex K q]
    exact hHS.symm
  have hsurj := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, hcard⟩).2
  let a : actualStandardIndex (n + 1) K (q + 1) := ⟨⟨α, Nat.lt_succ_self _⟩, hα⟩
  obtain ⟨c, hc⟩ := hsurj a
  have hval := congrArg (fun b : actualStandardIndex (n + 1) K (q + 1) => E b.val.val) hc
  have hcγ : c.val.val = γ := by
    simpa only [g, a, α, E.apply_symm_apply] using hval
  exact c.property (by rwa [hcγ])

/-- Actual minimal exponents are relabelled by the same exponent permutation. -/
def pivotFirstVertex (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualInitialVertices MonomialOrder.degLex (Ideal.map (pivotFirstRename f).toRingHom K) :=
  ⟨pivotFirstExponent f a.val, by
    have ha : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) a.val := by
      simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.property
    have hmin : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (pivotFirstRename f).toRingHom K)) (pivotFirstExponent f a.val) := by
      constructor
      · rw [actualInitialDiagram_pivotFirst K f hv]
        exact ⟨a.val, ha.prop, rfl⟩
      · intro γ hγ hle
        rw [actualInitialDiagram_pivotFirst K f hv] at hγ
        obtain ⟨β, hβ, rfl⟩ := hγ
        have hβa := (permuteExponent_le_iff (pivotFirstEquiv f) β a.val).mp hle
        exact (permuteExponent_le_iff (pivotFirstEquiv f) a.val β).mpr (ha.2 hβ hβa)
    simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hmin⟩

/-- The actual permuted labels exhaust the new actual vertex set. -/
theorem pivotFirstVertex_surjective
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0) :
    Function.Surjective (pivotFirstVertex K f hv) := by
  intro b
  have hb : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (pivotFirstRename f).toRingHom K)) b.val := by
    simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using b.property
  have hbD := hb.prop
  rw [actualInitialDiagram_pivotFirst K f hv] at hbD
  obtain ⟨α, hα, hαb⟩ := hbD
  have hmin : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) α := by
    refine ⟨hα, ?_⟩
    intro β hβ hβα
    have hEβ : pivotFirstExponent f β ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (pivotFirstRename f).toRingHom K) := by
      rw [actualInitialDiagram_pivotFirst K f hv]
      exact ⟨β, hβ, rfl⟩
    have hle : pivotFirstExponent f β ≤ b.val := by
      rw [← hαb]
      exact (permuteExponent_le_iff (pivotFirstEquiv f) β α).mpr hβα
    have hback := hb.2 hEβ hle
    rw [← hαb] at hback
    exact (permuteExponent_le_iff (pivotFirstEquiv f) α β).mp hback
  let a : actualInitialVertices MonomialOrder.degLex K :=
    ⟨α, by simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hmin⟩
  exact ⟨a, Subtype.ext hαb⟩

/-- Every actual promoted source vertex is transverse to the new first pivot. -/
theorem pivotFirstVertex_zero
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    (pivotFirstVertex K f hv a).val 0 = 0 := by
  change pivotFirstExponent f a.val 0 = 0
  rw [pivotFirstExponent_zero, hv a]

/-- Exact canonical covariance follows from the SAME whole diagram coefficients,
with the actual permuted original vertex label and no replacement family. -/
theorem pivotFirst_actualReducedVertexSeries
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    pivotFirstRename f (actualReducedVertexSeries MonomialOrder.degLex K a) =
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (pivotFirstRename f).toRingHom K) (pivotFirstVertex K f hv a) := by
  apply actualReducedVertexSeries_unique MonomialOrder.degLex
    (Ideal.map (pivotFirstRename f).toRingHom K) (pivotFirstVertex K f hv a) _
    (Ideal.mem_map_of_mem _ (actualReducedVertexSeries_mem MonomialOrder.degLex K a))
  intro γ hγ
  rw [actualInitialDiagram_pivotFirst K f hv] at hγ
  obtain ⟨β, hβ, rfl⟩ := hγ
  change MvPowerSeries.coeff (pivotFirstExponent f β)
      (pivotFirstRename f (actualReducedVertexSeries MonomialOrder.degLex K a)) =
    if pivotFirstExponent f β = pivotFirstExponent f a.val then 1 else 0
  rw [pivotFirstRename, pivotFirstExponent, coeff_rename_permuted,
    actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex K a β hβ]
  change (if β = a.val then 1 else 0) =
    (if pivotFirstExponent f β = pivotFirstExponent f a.val then 1 else 0)
  simp only [EquivLike.apply_eq_iff_eq]

end

end Hironaka.HironakaActualRelativeStandardnessPivotPriority
