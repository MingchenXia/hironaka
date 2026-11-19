import Hironaka.Resolution.HironakaG3RChartOfMember
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary

/-! # G3, target (A): a global locally finite simple normal crossings indexing of the glued boundary

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-global-snc.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (A-miss-2, global form).

* `not_eq_inter_of_isSNCDivisor`: two members at different positions of a simple normal crossings list never agree near
  a common point (their coordinate hyperplanes differ).
* `exists_boundary_extension`, `boundary_trace_mem`, `boundary_extension_unique`: for two charts with `U ⊆ U'`, the
  nonempty members of the boundary of the first are exactly the nonempty traces on `P⁻¹ U` of the members of the second,
  each extending uniquely.
* **`exists_isLocallyFiniteSNCDivisor_gluedBoundary`**: the boundary of a glued canonical resolution is the union of a
  locally finite family of nonempty closed sets forming a simple normal crossings divisor in the held indexed sense
  (`HironakaActualLocallyFiniteBoundary.IsLocallyFiniteSNCDivisor`); the members are the global boundary components,
  obtained from an exhaustion of `X` by relatively compact open sets over each of which `P` is a single canonical
  resolution (`HironakaG3RChartOfMember`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RGlobalSNC

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals NormalCrossings
  HironakaG3RGluedUniqueness HironakaG3RGluedBoundary
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ}

/-- **Members at different positions of a simple normal crossings list never agree near a common point.** -/
theorem not_eq_inter_of_isSNCDivisor {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {E : List (Set M)} (hE : IsSNCDivisor n E) {p q : Fin E.length} (hpq : p ≠ q)
    {O : Set M} (hO : IsOpen O) {x : M} (hxO : x ∈ O) (hxp : x ∈ E.get p) (heq : E.get p ∩ O = E.get q ∩ O) :
    False := by
  have key : ∀ y : M, y ∈ E.get p → y ∈ O → y ∈ E.get q := fun y h1 h2 => by
    have h : y ∈ E.get p ∩ O := ⟨h1, h2⟩
    rw [heq] at h
    exact h.1
  have hxq : x ∈ E.get q := key x hxp hxO
  obtain ⟨S, ⟨Φ, hsrc, hzero, hcoord⟩, hcard, hinj⟩ := hE.2 x
  have hSne : S p ≠ S q := fun h => hpq (hinj hxp hxq h)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hcard p hxp)
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (hcard q hxq)
  have hab : a ≠ b := fun h => hSne (by rw [ha, hb, h])
  have hxs : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  have h0t : (0 : ComplexModel n) ∈ Φ.target := hzero ▸ Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = (complexChartAt (n := n) x).val x := by
    rw [← hzero]; exact Φ.left_inv _ Φ.center_mem_source
  have h1 : ContinuousAt Φ.invFun 0 :=
    Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds h0t)
  have h2 : ContinuousAt (complexChartAt (n := n) x).val.symm (Φ.invFun 0) := by
    rw [hinv0]
    exact (complexChartAt (n := n) x).val.continuousAt_symm ((complexChartAt (n := n) x).val.map_source hxs)
  have hcont : ContinuousAt (fun v => (complexChartAt (n := n) x).val.symm (Φ.invFun v)) 0 :=
    ContinuousAt.comp h2 h1
  have hN : {v | v ∈ Φ.target ∧ (complexChartAt (n := n) x).val.symm (Φ.invFun v) ∈ O} ∈
      𝓝 (0 : ComplexModel n) := by
    refine Filter.inter_mem (Φ.isOpen_target.mem_nhds h0t) ?_
    have hx' : (complexChartAt (n := n) x).val.symm (Φ.invFun 0) ∈ O := by
      rw [hinv0, (complexChartAt (n := n) x).val.left_inv hxs]; exact hxO
    exact hcont.preimage_mem_nhds (hO.mem_nhds hx')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
  have htne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (ε / 2 : ℝ) ≠ 0)
  have hv : EuclideanSpace.single b ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ComplexModel n) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    have hn : ‖EuclideanSpace.single b ((ε / 2 : ℝ) : ℂ)‖ = ε / 2 := by
      simp [abs_of_pos hε]
    rw [hn]
    linarith
  obtain ⟨hvt, hvO⟩ := hball hv
  have hva : (EuclideanSpace.single b ((ε / 2 : ℝ) : ℂ) : ComplexModel n) a = 0 := by simp [hab]
  have hvb : (EuclideanSpace.single b ((ε / 2 : ℝ) : ℂ) : ComplexModel n) b = ((ε / 2 : ℝ) : ℂ) := by simp
  have hu : Φ.invFun (EuclideanSpace.single b ((ε / 2 : ℝ) : ℂ)) ∈ Φ.source := Φ.mapsTo_invFun hvt
  have hut : Φ.invFun (EuclideanSpace.single b ((ε / 2 : ℝ) : ℂ)) ∈ (complexChartAt (n := n) x).val.target := hsrc hu
  have hy := (complexChartAt (n := n) x).val.map_target hut
  have hψy := (complexChartAt (n := n) x).val.right_inv hut
  have hΦy : Φ.toFun ((complexChartAt (n := n) x).val ((complexChartAt (n := n) x).val.symm
      (Φ.invFun (EuclideanSpace.single b ((ε / 2 : ℝ) : ℂ))))) = EuclideanSpace.single b ((ε / 2 : ℝ) : ℂ) := by
    rw [hψy]; exact Φ.right_inv _ hvt
  have hyΦ : (complexChartAt (n := n) x).val ((complexChartAt (n := n) x).val.symm
      (Φ.invFun (EuclideanSpace.single b ((ε / 2 : ℝ) : ℂ)))) ∈ Φ.source := by rw [hψy]; exact hu
  have hyp := (hcoord p hxp hy hyΦ).mpr (by
    rw [hΦy, ha]
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact hva)
  have hyq := key _ hyp hvO
  have hc := (hcoord q hxq hy hyΦ).mp hyq
  rw [hΦy, hb] at hc
  have hcb := hc b (Finset.mem_singleton_self b)
  rw [hvb] at hcb
  exact htne hcb

/-! ### Boundaries of nested charts -/

section Nested

variable {X : CMfd.{u} n} {M : MarkedIdeal n X} (hM : IsInvDomain n M) {X' : CMfd.{u} n} {P : X' → X}

theorem inter_preimage_inf {c c' : GluedChart M X' P} (hcc' : c.U ≤ c'.U) {H : Set X'} (hH : H ∈ chartBoundary c) :
    H ∩ P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X) = H := by
  refine inter_eq_left.mpr fun y hy => ?_
  have hyV : y ∈ (c.V : Set X') := chartBoundary_subset_V c hH hy
  rw [c.V_eq] at hyV
  exact ⟨hyV, hcc' hyV⟩

theorem preimage_inf_eq {c c' : GluedChart M X' P} (hcc' : c.U ≤ c'.U) :
    P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X) = (c.V : Set X') := by
  rw [c.V_eq]
  ext y
  exact ⟨fun h => h.1, fun h => ⟨h, hcc' h⟩⟩

include hM

/-- **Extension**: a nonempty member of the boundary of `c` is the trace of a member of the boundary of `c'` (`U ⊆ U'`). -/
theorem exists_boundary_extension {c c' : GluedChart M X' P} (hcc' : c.U ≤ c'.U) {H : Set X'}
    (hH : H ∈ chartBoundary c) (hne : H.Nonempty) : ∃ H' ∈ chartBoundary c', H' ∩ c.V = H := by
  have h := chartBoundary_overlap hM c c'
  have hmem : H ∈ ((chartBoundary c).map (· ∩ P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X))).filter
      (fun H => decide H.Nonempty) := by
    refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨H, hH, inter_preimage_inf hcc' hH⟩, by simpa using hne⟩
  rw [h] at hmem
  obtain ⟨H', hH', he⟩ := List.mem_map.mp (List.mem_filter.mp hmem).1
  refine ⟨H', hH', ?_⟩
  rw [← preimage_inf_eq hcc']
  exact he

/-- **Traces**: the nonempty trace on `P⁻¹ U` of a member of the boundary of `c'` is a member of the boundary of `c`. -/
theorem boundary_trace_mem {c c' : GluedChart M X' P} (hcc' : c.U ≤ c'.U) {H' : Set X'}
    (hH' : H' ∈ chartBoundary c') (hne : (H' ∩ c.V).Nonempty) : H' ∩ c.V ∈ chartBoundary c := by
  have h := chartBoundary_overlap hM c c'
  have hmem : H' ∩ c.V ∈ ((chartBoundary c').map (· ∩ P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X))).filter
      (fun H => decide H.Nonempty) := by
    refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨H', hH', by rw [preimage_inf_eq hcc']⟩, by simpa using hne⟩
  rw [← h] at hmem
  obtain ⟨H, hH, he⟩ := List.mem_map.mp (List.mem_filter.mp hmem).1
  rw [← he, inter_preimage_inf hcc' hH]
  exact hH

/-- **Uniqueness of extensions**: two members of the boundary of `c'` with the same nonempty trace on `P⁻¹ U` are equal. -/
theorem boundary_extension_unique {c c' : GluedChart M X' P} {H₁ H₂ : Set X'}
    (h₁ : H₁ ∈ chartBoundary c') (h₂ : H₂ ∈ chartBoundary c') (hne : (H₁ ∩ c.V).Nonempty)
    (heq : H₁ ∩ c.V = H₂ ∩ c.V) : H₁ = H₂ := by
  have hsnc := isSNCDivisor_chartBoundary hM c'
  set E := (chartBoundary c').map ((Subtype.val : c'.V → X') ⁻¹' ·) with hE
  obtain ⟨p, hp⟩ := List.mem_iff_get.mp (List.mem_map_of_mem (f := ((Subtype.val : c'.V → X') ⁻¹' ·)) h₁)
  obtain ⟨q, hq⟩ := List.mem_iff_get.mp (List.mem_map_of_mem (f := ((Subtype.val : c'.V → X') ⁻¹' ·)) h₂)
  have hsub₁ := chartBoundary_subset_V c' h₁
  have hsub₂ := chartBoundary_subset_V c' h₂
  have hval : (Subtype.val : c'.V → X') ⁻¹' H₁ = (Subtype.val : c'.V → X') ⁻¹' H₂ → H₁ = H₂ := by
    intro h
    ext y
    constructor
    · intro hy
      have : (⟨y, hsub₁ hy⟩ : c'.V) ∈ (Subtype.val : c'.V → X') ⁻¹' H₂ := h ▸ hy
      exact this
    · intro hy
      have : (⟨y, hsub₂ hy⟩ : c'.V) ∈ (Subtype.val : c'.V → X') ⁻¹' H₁ := h.symm ▸ hy
      exact this
  by_cases hpq : p = q
  · subst hpq
    exact hval (hp.symm.trans hq)
  · exfalso
    obtain ⟨y, hyH, hyV⟩ := hne
    let O : Set c'.V := (Subtype.val : c'.V → X') ⁻¹' (c.V : Set X')
    have hO : IsOpen O := c.V.isOpen.preimage continuous_subtype_val
    refine not_eq_inter_of_isSNCDivisor hsnc hpq hO (x := ⟨y, hsub₁ hyH⟩) hyV (by rw [hp]; exact hyH) ?_
    rw [hp, hq]
    ext z
    constructor
    · rintro ⟨hz₁, hzO⟩
      have : (z : X') ∈ H₂ ∩ c.V := heq ▸ (⟨hz₁, hzO⟩ : (z : X') ∈ H₁ ∩ c.V)
      exact ⟨this.1, hzO⟩
    · rintro ⟨hz₂, hzO⟩
      have : (z : X') ∈ H₁ ∩ c.V := heq.symm ▸ (⟨hz₂, hzO⟩ : (z : X') ∈ H₂ ∩ c.V)
      exact ⟨this.1, hzO⟩

end Nested

/-! ### An exhaustion by single charts and the global members -/

section Global

variable {X : CMfd.{u} n} {M : MarkedIdeal n X} {X' : CMfd.{u} n} {P : X' → X}

/-- **An exhaustion of `X` by single charts**: charts `c k` of `P` with increasing bases whose saturated opens cover `X'`. -/
structure ChartExhaustion (M : MarkedIdeal n X) (X' : CMfd.{u} n) (P : X' → X) where
  /-- The charts. -/
  c : ℕ → GluedChart M X' P
  mono : ∀ {j k : ℕ}, j ≤ k → (c j).U ≤ (c k).U
  cover : ∀ y : X', ∃ k, y ∈ (c k).V

theorem exists_chartExhaustion (hM : IsInvDomain n M) (h : IsGluedCanonicalResolution M X' P) :
    Nonempty (ChartExhaustion M X' P) := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let K := CompactExhaustion.choice X
  have hU : ∀ k : ℕ, ∃ c : GluedChart M X' P, c.U = ⟨interior (K (k + 1)), isOpen_interior⟩ := fun k =>
    HironakaG3RChartOfMember.exists_gluedChart_of_subset_isCompact hM h _ (K.isCompact (k + 1)) interior_subset
  choose c hc using hU
  refine ⟨⟨c, fun {j k} hjk => ?_, fun y => ?_⟩⟩
  · rw [hc, hc]
    exact interior_mono (K.subset (by omega))
  · obtain ⟨k, hk⟩ := K.exists_mem (P y)
    refine ⟨k, (c k).mem_V ?_⟩
    rw [hc]
    exact K.subset_interior_succ k hk

variable (hM : IsInvDomain n M) (Ex : ChartExhaustion M X' P)

theorem ChartExhaustion.V_mono {j k : ℕ} (hjk : j ≤ k) : ((Ex.c j).V : Set X') ⊆ (Ex.c k).V := by
  intro y hy
  have h : y ∈ ((Ex.c j).V : Set X') := hy
  rw [(Ex.c j).V_eq] at h
  exact (Ex.c k).mem_V (Ex.mono hjk h)

/-- **A global member of the boundary**: a nonempty set whose trace on each `P⁻¹ U_k` is empty or a member of the
boundary of the `k`-th chart. -/
def IsGlobalMember (D : Set X') : Prop :=
  D.Nonempty ∧ ∀ k, D ∩ (Ex.c k).V = ∅ ∨ D ∩ (Ex.c k).V ∈ chartBoundary (Ex.c k)

theorem IsGlobalMember.mem_of_nonempty {D : Set X'} (hD : IsGlobalMember Ex D) (k : ℕ)
    (hne : (D ∩ (Ex.c k).V).Nonempty) : D ∩ (Ex.c k).V ∈ chartBoundary (Ex.c k) :=
  (hD.2 k).resolve_left hne.ne_empty

include hM

/-- One extension step along the exhaustion. -/
theorem ext_step {k m : ℕ} {H : Set X'} (hH : H ∈ chartBoundary (Ex.c (k + m))) (hne : H.Nonempty) :
    ∃ H' ∈ chartBoundary (Ex.c (k + (m + 1))), H' ∩ (Ex.c (k + m)).V = H :=
  exists_boundary_extension hM (Ex.mono (by omega)) hH hne

/-- The successive extensions of a nonempty member of the `k`-th boundary. -/
def extSeq (k : ℕ) (H : Set X') (hH : H ∈ chartBoundary (Ex.c k)) (hne : H.Nonempty) :
    (m : ℕ) → {H' : Set X' // H' ∈ chartBoundary (Ex.c (k + m)) ∧ H' ∩ (Ex.c k).V = H}
  | 0 => ⟨H, hH, inter_eq_left.mpr (chartBoundary_subset_V _ hH)⟩
  | m + 1 =>
    let p := extSeq k H hH hne m
    have hpne : p.1.Nonempty := by
      obtain ⟨y, hy⟩ := hne
      rw [← p.2.2] at hy
      exact ⟨y, hy.1⟩
    ⟨(ext_step hM Ex p.2.1 hpne).choose, (ext_step hM Ex p.2.1 hpne).choose_spec.1, by
      have h1 := (ext_step hM Ex p.2.1 hpne).choose_spec.2
      have hsub := Ex.V_mono (j := k) (k := k + m) (by omega)
      calc _ = ((ext_step hM Ex p.2.1 hpne).choose ∩ (Ex.c (k + m)).V) ∩ (Ex.c k).V := by
              rw [inter_assoc, inter_eq_right.mpr hsub]
        _ = p.1 ∩ (Ex.c k).V := by rw [h1]
        _ = H := p.2.2⟩

theorem extSeq_nonempty (k : ℕ) (H : Set X') (hH : H ∈ chartBoundary (Ex.c k)) (hne : H.Nonempty) (m : ℕ) :
    (extSeq hM Ex k H hH hne m).1.Nonempty := by
  have h2 := (extSeq hM Ex k H hH hne m).2.2
  refine hne.mono fun y hy => ?_
  rw [← h2] at hy
  exact hy.1

theorem extSeq_succ_inter (k : ℕ) (H : Set X') (hH : H ∈ chartBoundary (Ex.c k)) (hne : H.Nonempty) (m : ℕ) :
    (extSeq hM Ex k H hH hne (m + 1)).1 ∩ (Ex.c (k + m)).V = (extSeq hM Ex k H hH hne m).1 :=
  (ext_step hM Ex (extSeq hM Ex k H hH hne m).2.1 (extSeq_nonempty hM Ex k H hH hne m)).choose_spec.2

theorem extSeq_inter (k : ℕ) (H : Set X') (hH : H ∈ chartBoundary (Ex.c k)) (hne : H.Nonempty) (m d : ℕ) :
    (extSeq hM Ex k H hH hne (m + d)).1 ∩ (Ex.c (k + m)).V = (extSeq hM Ex k H hH hne m).1 := by
  induction d with
  | zero => exact inter_eq_left.mpr (chartBoundary_subset_V _ (extSeq hM Ex k H hH hne m).2.1)
  | succ d ih =>
    have h1 := extSeq_succ_inter hM Ex k H hH hne (m + d)
    have hsub := Ex.V_mono (j := k + m) (k := k + (m + d)) (by omega)
    rw [← Nat.add_assoc m d 1, ← ih, ← h1, inter_assoc, inter_eq_right.mpr hsub]

/-- **Existence of global members**: a nonempty member of the `k`-th boundary is the trace of a global member. -/
theorem exists_globalMember (k : ℕ) {H : Set X'} (hH : H ∈ chartBoundary (Ex.c k)) (hne : H.Nonempty) :
    ∃ D, IsGlobalMember Ex D ∧ D ∩ (Ex.c k).V = H := by
  let e := extSeq hM Ex k H hH hne
  let D := ⋃ m, (e m).1
  have hmono : ∀ m d, (e m).1 ⊆ (e (m + d)).1 := fun m d y hy => by
    rw [← extSeq_inter hM Ex k H hH hne m d] at hy
    exact hy.1
  have htr : ∀ m, D ∩ (Ex.c (k + m)).V = (e m).1 := by
    intro m
    apply Subset.antisymm
    · rintro y ⟨hy, hyV⟩
      obtain ⟨m', hm'⟩ := mem_iUnion.mp hy
      rcases le_total m m' with hle | hle
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
        rw [← extSeq_inter hM Ex k H hH hne m d]
        exact ⟨hm', hyV⟩
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
        exact hmono m' d hm'
    · intro y hy
      exact ⟨mem_iUnion.mpr ⟨m, hy⟩, chartBoundary_subset_V _ (e m).2.1 hy⟩
  have hk : D ∩ (Ex.c k).V = H := htr 0
  refine ⟨D, ⟨?_, fun j => ?_⟩, hk⟩
  · obtain ⟨y, hy⟩ := hne
    exact ⟨y, mem_iUnion.mpr ⟨0, hy⟩⟩
  · rcases le_total k j with hle | hle
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
      right
      rw [htr m]
      exact (e m).2.1
    · have hsub := Ex.V_mono hle
      have hDj : D ∩ (Ex.c j).V = H ∩ (Ex.c j).V := by
        rw [← hk, inter_assoc, inter_eq_right.mpr hsub]
      rw [hDj]
      by_cases hne' : (H ∩ (Ex.c j).V).Nonempty
      · exact Or.inr (boundary_trace_mem hM (Ex.mono hle) hH hne')
      · exact Or.inl (not_nonempty_iff_eq_empty.mp hne')

/-- **Uniqueness of global members**: two global members with the same nonempty trace on some `P⁻¹ U_k` are equal. -/
theorem globalMember_unique {D D' : Set X'} (hD : IsGlobalMember Ex D) (hD' : IsGlobalMember Ex D') (k : ℕ)
    (hne : (D ∩ (Ex.c k).V).Nonempty) (heq : D ∩ (Ex.c k).V = D' ∩ (Ex.c k).V) : D = D' := by
  have htr : ∀ j, D ∩ (Ex.c j).V = D' ∩ (Ex.c j).V := by
    intro j
    rcases le_total j k with hle | hle
    · have hsub := Ex.V_mono hle
      rw [← inter_eq_right.mpr hsub, ← inter_assoc, heq, inter_assoc]
    · have hsub := Ex.V_mono hle
      have hne₁ : (D ∩ (Ex.c j).V).Nonempty := hne.mono (inter_subset_inter_right _ hsub)
      have hne₂ : (D' ∩ (Ex.c j).V).Nonempty := (heq ▸ hne).mono (inter_subset_inter_right _ hsub)
      have hk₁ : D ∩ (Ex.c j).V ∩ (Ex.c k).V = D ∩ (Ex.c k).V := by
        rw [inter_assoc, inter_eq_right.mpr hsub]
      have hk₂ : D' ∩ (Ex.c j).V ∩ (Ex.c k).V = D' ∩ (Ex.c k).V := by
        rw [inter_assoc, inter_eq_right.mpr hsub]
      exact boundary_extension_unique hM (c := Ex.c k) (hD.mem_of_nonempty Ex j hne₁) (hD'.mem_of_nonempty Ex j hne₂)
        (by rw [hk₁]; exact hne) (by rw [hk₁, hk₂, heq])
  ext y
  obtain ⟨j, hj⟩ := Ex.cover y
  constructor
  · intro hy
    exact ((htr j ▸ (⟨hy, hj⟩ : y ∈ D ∩ (Ex.c j).V)) : y ∈ D' ∩ (Ex.c j).V).1
  · intro hy
    exact (((htr j).symm ▸ (⟨hy, hj⟩ : y ∈ D' ∩ (Ex.c j).V)) : y ∈ D ∩ (Ex.c j).V).1

end Global

/-! ### The global members form a locally finite simple normal crossings family -/

section Main

variable {X : CMfd.{u} n} {M : MarkedIdeal n X} {X' : CMfd.{u} n} {P : X' → X}
  (hM : IsInvDomain n M) (Ex : ChartExhaustion M X' P)
include hM

theorem iUnion_globalMember :
    (⋃ i : {D : Set X' // IsGlobalMember Ex D}, (i : Set X')) = gluedBoundary M X' P := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨⟨D, hD⟩, hyD⟩ := mem_iUnion.mp hy
    obtain ⟨k, hk⟩ := Ex.cover y
    have hmem := hD.mem_of_nonempty Ex k ⟨y, hyD, hk⟩
    have h := gluedBoundary_inter_V hM (Ex.c k)
    have hy' : y ∈ ⋃ H ∈ chartBoundary (Ex.c k), H := mem_biUnion hmem ⟨hyD, hk⟩
    rw [← h] at hy'
    exact hy'.1
  · intro y hy
    obtain ⟨k, hk⟩ := Ex.cover y
    have h := gluedBoundary_inter_V hM (Ex.c k)
    have hy' : y ∈ ⋃ H ∈ chartBoundary (Ex.c k), H := by rw [← h]; exact ⟨hy, hk⟩
    obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hy'
    obtain ⟨D, hD, hDk⟩ := exists_globalMember hM Ex k hH ⟨y, hyH⟩
    refine mem_iUnion.mpr ⟨⟨D, hD⟩, ?_⟩
    have hyD : y ∈ D ∩ (Ex.c k).V := by rw [hDk]; exact hyH
    exact hyD.1

theorem isClosed_globalMember {D : Set X'} (hD : IsGlobalMember Ex D) : IsClosed D := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨k, hk⟩ := Ex.cover z
  have hsnc := isSNCDivisor_chartBoundary hM (Ex.c k)
  have hpre : (Subtype.val : (Ex.c k).V → X') ⁻¹' (D ∩ (Ex.c k).V) = (Subtype.val : (Ex.c k).V → X') ⁻¹' D := by
    ext q
    exact ⟨fun h => h.1, fun h => ⟨h, q.2⟩⟩
  have hcl : IsClosed ((Subtype.val : (Ex.c k).V → X') ⁻¹' D) := by
    rw [← hpre]
    rcases hD.2 k with h | h
    · rw [h, preimage_empty]
      exact isClosed_empty
    · exact hsnc.1 _ (List.mem_map_of_mem (f := ((Subtype.val : (Ex.c k).V → X') ⁻¹' ·)) h)
  refine ⟨Subtype.val '' ((Subtype.val : (Ex.c k).V → X') ⁻¹' D)ᶜ, ?_,
    (Ex.c k).V.isOpen.isOpenMap_subtype_val _ hcl.isOpen_compl, ⟨⟨z, hk⟩, hz, rfl⟩⟩
  rintro _ ⟨q, hq, rfl⟩ hqD
  exact hq hqD

theorem locallyFinite_globalMember :
    LocallyFinite (fun i : {D : Set X' // IsGlobalMember Ex D} => (i : Set X')) := by
  intro z
  obtain ⟨k, hk⟩ := Ex.cover z
  refine ⟨(Ex.c k).V, (Ex.c k).V.isOpen.mem_nhds hk, ?_⟩
  have hinj : Set.InjOn (fun i : {D : Set X' // IsGlobalMember Ex D} => (i : Set X') ∩ (Ex.c k).V)
      {i | ((i : Set X') ∩ (Ex.c k).V).Nonempty} := by
    intro i hi j _ hij
    exact Subtype.ext (globalMember_unique hM Ex i.2 j.2 k hi hij)
  refine Set.Finite.of_finite_image ?_ hinj
  refine (List.finite_toSet (chartBoundary (Ex.c k))).subset ?_
  rintro _ ⟨i, hi, rfl⟩
  exact i.2.mem_of_nonempty Ex k hi

theorem coordinates_globalMember (x : X') :
    ∃ S : {D : Set X' // IsGlobalMember Ex D} → Finset (Fin n),
      IsCoordinateFamilyAt n (fun i : {D : Set X' // IsGlobalMember Ex D} => (i : Set X')) S x ∧
        (∀ i : {D : Set X' // IsGlobalMember Ex D}, x ∈ (i : Set X') → (S i).card = 1) ∧
        Set.InjOn S {i : {D : Set X' // IsGlobalMember Ex D} | x ∈ (i : Set X')} := by
  obtain ⟨k, hk⟩ := Ex.cover x
  have hsnc := isSNCDivisor_chartBoundary hM (Ex.c k)
  obtain ⟨S, ⟨Φ, hsrc, hzero, hcoord⟩, hcard, hinj⟩ := hsnc.2 ⟨x, hk⟩
  have hpos : ∀ i : {D : Set X' // IsGlobalMember Ex D}, ((i : Set X') ∩ (Ex.c k).V) ∈ chartBoundary (Ex.c k) →
      ∃ p : Fin ((chartBoundary (Ex.c k)).map ((Subtype.val : (Ex.c k).V → X') ⁻¹' ·)).length,
        ((chartBoundary (Ex.c k)).map ((Subtype.val : (Ex.c k).V → X') ⁻¹' ·)).get p =
          (Subtype.val : (Ex.c k).V → X') ⁻¹' (i : Set X') := fun i hi => by
    obtain ⟨p, hp⟩ := List.mem_iff_get.mp (List.mem_map_of_mem (f := ((Subtype.val : (Ex.c k).V → X') ⁻¹' ·)) hi)
    refine ⟨p, hp.trans ?_⟩
    ext q
    exact ⟨fun h => h.1, fun h => ⟨h, q.2⟩⟩
  let S' : {D : Set X' // IsGlobalMember Ex D} → Finset (Fin n) := fun i =>
    if hi : ((i : Set X') ∩ (Ex.c k).V) ∈ chartBoundary (Ex.c k) then S (hpos i hi).choose else ∅
  have hmemx : ∀ i : {D : Set X' // IsGlobalMember Ex D}, x ∈ (i : Set X') →
      ((i : Set X') ∩ (Ex.c k).V) ∈ chartBoundary (Ex.c k) :=
    fun i hx => i.2.mem_of_nonempty Ex k ⟨x, hx, hk⟩
  have hS' : ∀ (i : {D : Set X' // IsGlobalMember Ex D}) (hx : x ∈ (i : Set X')), S' i = S (hpos i (hmemx i hx)).choose :=
    fun i hx => dif_pos (hmemx i hx)
  have hget : ∀ (i : {D : Set X' // IsGlobalMember Ex D}) (hx : x ∈ (i : Set X')),
      ((chartBoundary (Ex.c k)).map ((Subtype.val : (Ex.c k).V → X') ⁻¹' ·)).get (hpos i (hmemx i hx)).choose =
        (Subtype.val : (Ex.c k).V → X') ⁻¹' (i : Set X') := fun i hx => (hpos i (hmemx i hx)).choose_spec
  refine ⟨S', ?_, ?_, ?_⟩
  · apply (NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff (x := (⟨x, hk⟩ : (Ex.c k).V))).mp
    refine ⟨Φ, hsrc, hzero, fun i hxi y hy hyΦ => ?_⟩
    have hxi' : x ∈ (i : Set X') := hxi
    rw [hS' i hxi']
    have h := hcoord (hpos i (hmemx i hxi')).choose (by beta_reduce; rw [hget i hxi']; exact hxi) hy hyΦ
    beta_reduce at h
    rw [hget i hxi'] at h
    exact h
  · intro i hxi
    rw [hS' i hxi]
    exact hcard _ (by rw [hget i hxi]; exact hxi)
  · intro i hi j hj hij
    have hi' : x ∈ (i : Set X') := hi
    have hj' : x ∈ (j : Set X') := hj
    rw [hS' i hi', hS' j hj'] at hij
    have hp := hinj (by rw [Set.mem_ofPred_eq, hget i hi']; exact hi') (by rw [Set.mem_ofPred_eq, hget j hj']; exact hj') hij
    have hE : (Subtype.val : (Ex.c k).V → X') ⁻¹' (i : Set X') = (Subtype.val : (Ex.c k).V → X') ⁻¹' (j : Set X') := by
      rw [← hget i hi', ← hget j hj', hp]
    have hinter : (i : Set X') ∩ (Ex.c k).V = (j : Set X') ∩ (Ex.c k).V := by
      ext y
      constructor
      · rintro ⟨hy, hyV⟩
        have hy' : (⟨y, hyV⟩ : (Ex.c k).V) ∈ (Subtype.val : (Ex.c k).V → X') ⁻¹' (j : Set X') := hE ▸ hy
        exact ⟨hy', hyV⟩
      · rintro ⟨hy, hyV⟩
        have hy' : (⟨y, hyV⟩ : (Ex.c k).V) ∈ (Subtype.val : (Ex.c k).V → X') ⁻¹' (i : Set X') := hE.symm ▸ hy
        exact ⟨hy', hyV⟩
    exact Subtype.ext (globalMember_unique hM Ex i.2 j.2 k ⟨x, hi', hk⟩ hinter)

/-- **Global simple normal crossings of the glued boundary** (A-miss-2, global form): the boundary of a glued canonical
resolution is the union of a locally finite family of nonempty closed sets which is a simple normal crossings divisor in the
indexed sense of `HironakaActualLocallyFiniteBoundary.IsLocallyFiniteSNCDivisor`. -/
theorem exists_isLocallyFiniteSNCDivisor_gluedBoundary (h : IsGluedCanonicalResolution M X' P) :
    ∃ (ι : Type u) (D : ι → Set X'), HironakaActualLocallyFiniteBoundary.IsLocallyFiniteSNCDivisor n D ∧
      (∀ i, (D i).Nonempty) ∧ (⋃ i, D i) = gluedBoundary M X' P := by
  obtain ⟨Ex⟩ := exists_chartExhaustion hM h
  exact ⟨{D : Set X' // IsGlobalMember Ex D}, fun i => i.1,
    ⟨locallyFinite_globalMember hM Ex, fun i => isClosed_globalMember hM Ex i.2, coordinates_globalMember hM Ex⟩,
    fun i => i.2.1, iUnion_globalMember hM Ex⟩

end Main

end

end Hironaka.HironakaG3RGlobalSNC
