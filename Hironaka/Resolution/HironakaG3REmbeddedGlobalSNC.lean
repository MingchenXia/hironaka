import Hironaka.Resolution.HironakaG3REmbeddedBoundary

/-! # G3: global simple normal crossings from compatible exhaustions; the embedded boundary

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-embedded-global-snc.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md`.

* **`SNCExhaustion X'`** (generic): an increasing exhaustion of `X'` by open sets `W k` carrying simple normal crossings
  lists `B k` (members in `W k`) whose nonempty traces on `W j` (`j ≤ k`) are the nonempty members of `B j`.
  **`SNCExhaustion.exists_isLocallyFiniteSNCDivisor`**: the members glue to a locally finite indexed simple normal
  crossings family (`HironakaActualLocallyFiniteBoundary.IsLocallyFiniteSNCDivisor`) of nonempty closed sets with union
  `⋃ k, ⋃ B k`.  (The construction of `HironakaG3RGlobalSNC`, abstracted.)
* **`exists_isLocallyFiniteSNCDivisor_exceptionalLocus`**: for every glued embedded resolution `P : X' → X` of `V`, the
  exceptional locus `Exc P = P⁻¹ V_sing` is the union of a locally finite indexed simple normal crossings family of nonempty
  closed sets (global form of the chart-wise boundary of `HironakaG3RGluedEmbedded`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3REmbeddedGlobalSNC

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.NonKahlerLocus Hironaka.BlowupSequences BlowupTowers MarkedIdeals NormalCrossings
  HironakaG3RTowerClass HironakaG3RGluedEmbedded HironakaG3RGlobalSNC

variable {n : ℕ}

/-- **A compatible exhaustion by simple normal crossings lists.** -/
structure SNCExhaustion (X' : CMfd.{u} n) where
  /-- The exhausting open sets. -/
  W : ℕ → Opens X'
  /-- The lists. -/
  B : ℕ → List (Set X')
  mono : ∀ {j k : ℕ}, j ≤ k → (W j : Set X') ⊆ W k
  cover : ∀ y : X', ∃ k, y ∈ W k
  sub : ∀ {k : ℕ} {H : Set X'}, H ∈ B k → H ⊆ W k
  snc : ∀ k, IsSNCDivisor n ((B k).map ((Subtype.val : W k → X') ⁻¹' ·))
  nested : ∀ {j k : ℕ}, j ≤ k →
    ((B k).map (· ∩ (W j : Set X'))).filter (fun H => decide H.Nonempty) = (B j).filter (fun H => decide H.Nonempty)

namespace SNCExhaustion

variable {X' : CMfd.{u} n} (Ex : SNCExhaustion X')

theorem exists_ext {j k : ℕ} (hjk : j ≤ k) {H : Set X'} (hH : H ∈ Ex.B j) (hne : H.Nonempty) :
    ∃ H' ∈ Ex.B k, H' ∩ Ex.W j = H := by
  have hmem : H ∈ (Ex.B j).filter (fun H => decide H.Nonempty) := List.mem_filter.mpr ⟨hH, by simpa using hne⟩
  rw [← Ex.nested hjk] at hmem
  obtain ⟨H', hH', he⟩ := List.mem_map.mp (List.mem_filter.mp hmem).1
  exact ⟨H', hH', he⟩

theorem trace_mem {j k : ℕ} (hjk : j ≤ k) {H' : Set X'} (hH' : H' ∈ Ex.B k) (hne : (H' ∩ Ex.W j).Nonempty) :
    H' ∩ Ex.W j ∈ Ex.B j := by
  have hmem : H' ∩ Ex.W j ∈ ((Ex.B k).map (· ∩ (Ex.W j : Set X'))).filter (fun H => decide H.Nonempty) :=
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨H', hH', rfl⟩, by simpa using hne⟩
  rw [Ex.nested hjk] at hmem
  exact (List.mem_filter.mp hmem).1

theorem ext_unique {j k : ℕ} {H₁ H₂ : Set X'} (h₁ : H₁ ∈ Ex.B k) (h₂ : H₂ ∈ Ex.B k) (hne : (H₁ ∩ Ex.W j).Nonempty)
    (heq : H₁ ∩ Ex.W j = H₂ ∩ Ex.W j) : H₁ = H₂ := by
  obtain ⟨p, hp⟩ := List.mem_iff_get.mp (List.mem_map_of_mem (f := ((Subtype.val : Ex.W k → X') ⁻¹' ·)) h₁)
  obtain ⟨q, hq⟩ := List.mem_iff_get.mp (List.mem_map_of_mem (f := ((Subtype.val : Ex.W k → X') ⁻¹' ·)) h₂)
  have hsub₁ := Ex.sub h₁
  have hsub₂ := Ex.sub h₂
  have hval : (Subtype.val : Ex.W k → X') ⁻¹' H₁ = (Subtype.val : Ex.W k → X') ⁻¹' H₂ → H₁ = H₂ := by
    intro h
    ext y
    constructor
    · intro hy
      have : (⟨y, hsub₁ hy⟩ : Ex.W k) ∈ (Subtype.val : Ex.W k → X') ⁻¹' H₂ := h ▸ hy
      exact this
    · intro hy
      have : (⟨y, hsub₂ hy⟩ : Ex.W k) ∈ (Subtype.val : Ex.W k → X') ⁻¹' H₁ := h.symm ▸ hy
      exact this
  by_cases hpq : p = q
  · subst hpq
    exact hval (hp.symm.trans hq)
  · exfalso
    obtain ⟨y, hyH, hyV⟩ := hne
    let O : Set (Ex.W k) := (Subtype.val : Ex.W k → X') ⁻¹' (Ex.W j : Set X')
    have hO : IsOpen O := (Ex.W j).isOpen.preimage continuous_subtype_val
    refine not_eq_inter_of_isSNCDivisor (Ex.snc k) hpq hO (x := ⟨y, hsub₁ hyH⟩) hyV (by rw [hp]; exact hyH) ?_
    rw [hp, hq]
    ext z
    constructor
    · rintro ⟨hz₁, hzO⟩
      have : (z : X') ∈ H₂ ∩ Ex.W j := heq ▸ (⟨hz₁, hzO⟩ : (z : X') ∈ H₁ ∩ Ex.W j)
      exact ⟨this.1, hzO⟩
    · rintro ⟨hz₂, hzO⟩
      have : (z : X') ∈ H₁ ∩ Ex.W j := heq.symm ▸ (⟨hz₂, hzO⟩ : (z : X') ∈ H₂ ∩ Ex.W j)
      exact ⟨this.1, hzO⟩

/-- **A global member**: nonempty, with trace on each `W k` empty or a member of `B k`. -/
def IsGlobalMember (D : Set X') : Prop :=
  D.Nonempty ∧ ∀ k, D ∩ Ex.W k = ∅ ∨ D ∩ Ex.W k ∈ Ex.B k

theorem IsGlobalMember.mem_of_nonempty {D : Set X'} (hD : Ex.IsGlobalMember D) (k : ℕ)
    (hne : (D ∩ Ex.W k).Nonempty) : D ∩ Ex.W k ∈ Ex.B k :=
  (hD.2 k).resolve_left hne.ne_empty

/-- The successive extensions of a nonempty member of `B k`. -/
def extSeq (k : ℕ) (H : Set X') (hH : H ∈ Ex.B k) (hne : H.Nonempty) :
    (m : ℕ) → {H' : Set X' // H' ∈ Ex.B (k + m) ∧ H' ∩ Ex.W k = H}
  | 0 => ⟨H, hH, inter_eq_left.mpr (Ex.sub hH)⟩
  | m + 1 =>
    let p := extSeq k H hH hne m
    have hpne : p.1.Nonempty := by
      obtain ⟨y, hy⟩ := hne
      rw [← p.2.2] at hy
      exact ⟨y, hy.1⟩
    ⟨(Ex.exists_ext (j := k + m) (k := k + (m + 1)) (by omega) p.2.1 hpne).choose,
      (Ex.exists_ext (j := k + m) (k := k + (m + 1)) (by omega) p.2.1 hpne).choose_spec.1, by
      have h1 := (Ex.exists_ext (j := k + m) (k := k + (m + 1)) (by omega) p.2.1 hpne).choose_spec.2
      have hsub := Ex.mono (j := k) (k := k + m) (by omega)
      calc _ = ((Ex.exists_ext (j := k + m) (k := k + (m + 1)) (by omega) p.2.1 hpne).choose ∩ Ex.W (k + m)) ∩
              Ex.W k := by rw [inter_assoc, inter_eq_right.mpr hsub]
        _ = p.1 ∩ Ex.W k := by rw [h1]
        _ = H := p.2.2⟩

theorem extSeq_nonempty (k : ℕ) (H : Set X') (hH : H ∈ Ex.B k) (hne : H.Nonempty) (m : ℕ) :
    (Ex.extSeq k H hH hne m).1.Nonempty := by
  have h2 := (Ex.extSeq k H hH hne m).2.2
  refine hne.mono fun y hy => ?_
  rw [← h2] at hy
  exact hy.1

theorem extSeq_succ_inter (k : ℕ) (H : Set X') (hH : H ∈ Ex.B k) (hne : H.Nonempty) (m : ℕ) :
    (Ex.extSeq k H hH hne (m + 1)).1 ∩ Ex.W (k + m) = (Ex.extSeq k H hH hne m).1 :=
  (Ex.exists_ext (j := k + m) (k := k + (m + 1)) (by omega) (Ex.extSeq k H hH hne m).2.1
    (Ex.extSeq_nonempty k H hH hne m)).choose_spec.2

theorem extSeq_inter (k : ℕ) (H : Set X') (hH : H ∈ Ex.B k) (hne : H.Nonempty) (m d : ℕ) :
    (Ex.extSeq k H hH hne (m + d)).1 ∩ Ex.W (k + m) = (Ex.extSeq k H hH hne m).1 := by
  induction d with
  | zero => exact inter_eq_left.mpr (Ex.sub (Ex.extSeq k H hH hne m).2.1)
  | succ d ih =>
    have h1 := Ex.extSeq_succ_inter k H hH hne (m + d)
    have hsub := Ex.mono (j := k + m) (k := k + (m + d)) (by omega)
    rw [← Nat.add_assoc m d 1, ← ih, ← h1, inter_assoc, inter_eq_right.mpr hsub]

theorem exists_globalMember (k : ℕ) {H : Set X'} (hH : H ∈ Ex.B k) (hne : H.Nonempty) :
    ∃ D, Ex.IsGlobalMember D ∧ D ∩ Ex.W k = H := by
  let e := Ex.extSeq k H hH hne
  let D := ⋃ m, (e m).1
  have hmono : ∀ m d, (e m).1 ⊆ (e (m + d)).1 := fun m d y hy => by
    rw [← Ex.extSeq_inter k H hH hne m d] at hy
    exact hy.1
  have htr : ∀ m, D ∩ Ex.W (k + m) = (e m).1 := by
    intro m
    apply Subset.antisymm
    · rintro y ⟨hy, hyV⟩
      obtain ⟨m', hm'⟩ := mem_iUnion.mp hy
      rcases le_total m m' with hle | hle
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
        rw [← Ex.extSeq_inter k H hH hne m d]
        exact ⟨hm', hyV⟩
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
        exact hmono m' d hm'
    · intro y hy
      exact ⟨mem_iUnion.mpr ⟨m, hy⟩, Ex.sub (e m).2.1 hy⟩
  have hk : D ∩ Ex.W k = H := htr 0
  refine ⟨D, ⟨?_, fun j => ?_⟩, hk⟩
  · obtain ⟨y, hy⟩ := hne
    exact ⟨y, mem_iUnion.mpr ⟨0, hy⟩⟩
  · rcases le_total k j with hle | hle
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
      right
      rw [htr m]
      exact (e m).2.1
    · have hsub := Ex.mono hle
      have hDj : D ∩ Ex.W j = H ∩ Ex.W j := by
        rw [← hk, inter_assoc, inter_eq_right.mpr hsub]
      rw [hDj]
      by_cases hne' : (H ∩ Ex.W j).Nonempty
      · exact Or.inr (Ex.trace_mem hle hH hne')
      · exact Or.inl (not_nonempty_iff_eq_empty.mp hne')

theorem globalMember_unique {D D' : Set X'} (hD : Ex.IsGlobalMember D) (hD' : Ex.IsGlobalMember D') (k : ℕ)
    (hne : (D ∩ Ex.W k).Nonempty) (heq : D ∩ Ex.W k = D' ∩ Ex.W k) : D = D' := by
  have htr : ∀ j, D ∩ Ex.W j = D' ∩ Ex.W j := by
    intro j
    rcases le_total j k with hle | hle
    · have hsub := Ex.mono hle
      rw [← inter_eq_right.mpr hsub, ← inter_assoc, heq, inter_assoc]
    · have hsub := Ex.mono hle
      have hne₁ : (D ∩ Ex.W j).Nonempty := hne.mono (inter_subset_inter_right _ hsub)
      have hne₂ : (D' ∩ Ex.W j).Nonempty := (heq ▸ hne).mono (inter_subset_inter_right _ hsub)
      have hk₁ : D ∩ Ex.W j ∩ Ex.W k = D ∩ Ex.W k := by rw [inter_assoc, inter_eq_right.mpr hsub]
      have hk₂ : D' ∩ Ex.W j ∩ Ex.W k = D' ∩ Ex.W k := by rw [inter_assoc, inter_eq_right.mpr hsub]
      exact Ex.ext_unique (hD.mem_of_nonempty Ex j hne₁) (hD'.mem_of_nonempty Ex j hne₂)
        (by rw [hk₁]; exact hne) (by rw [hk₁, hk₂, heq])
  ext y
  obtain ⟨j, hj⟩ := Ex.cover y
  constructor
  · intro hy
    exact ((htr j ▸ (⟨hy, hj⟩ : y ∈ D ∩ Ex.W j)) : y ∈ D' ∩ Ex.W j).1
  · intro hy
    exact (((htr j).symm ▸ (⟨hy, hj⟩ : y ∈ D' ∩ Ex.W j)) : y ∈ D ∩ Ex.W j).1

theorem iUnion_globalMember :
    (⋃ i : {D : Set X' // Ex.IsGlobalMember D}, (i : Set X')) = ⋃ k, ⋃ H ∈ Ex.B k, H := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨⟨D, hD⟩, hyD⟩ := mem_iUnion.mp hy
    obtain ⟨k, hk⟩ := Ex.cover y
    exact mem_iUnion.mpr ⟨k, mem_biUnion (hD.mem_of_nonempty Ex k ⟨y, hyD, hk⟩) ⟨hyD, hk⟩⟩
  · intro y hy
    obtain ⟨k, hy⟩ := mem_iUnion.mp hy
    obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hy
    obtain ⟨D, hD, hDk⟩ := Ex.exists_globalMember k hH ⟨y, hyH⟩
    refine mem_iUnion.mpr ⟨⟨D, hD⟩, ?_⟩
    have hyD : y ∈ D ∩ Ex.W k := by rw [hDk]; exact hyH
    exact hyD.1

theorem isClosed_globalMember {D : Set X'} (hD : Ex.IsGlobalMember D) : IsClosed D := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨k, hk⟩ := Ex.cover z
  have hpre : (Subtype.val : Ex.W k → X') ⁻¹' (D ∩ Ex.W k) = (Subtype.val : Ex.W k → X') ⁻¹' D := by
    ext q
    exact ⟨fun h => h.1, fun h => ⟨h, q.2⟩⟩
  have hcl : IsClosed ((Subtype.val : Ex.W k → X') ⁻¹' D) := by
    rw [← hpre]
    rcases hD.2 k with h | h
    · rw [h, preimage_empty]
      exact isClosed_empty
    · exact (Ex.snc k).1 _ (List.mem_map_of_mem (f := ((Subtype.val : Ex.W k → X') ⁻¹' ·)) h)
  refine ⟨Subtype.val '' ((Subtype.val : Ex.W k → X') ⁻¹' D)ᶜ, ?_,
    (Ex.W k).isOpen.isOpenMap_subtype_val _ hcl.isOpen_compl, ⟨⟨z, hk⟩, hz, rfl⟩⟩
  rintro _ ⟨q, hq, rfl⟩ hqD
  exact hq hqD

theorem locallyFinite_globalMember :
    LocallyFinite (fun i : {D : Set X' // Ex.IsGlobalMember D} => (i : Set X')) := by
  intro z
  obtain ⟨k, hk⟩ := Ex.cover z
  refine ⟨Ex.W k, (Ex.W k).isOpen.mem_nhds hk, ?_⟩
  have hinj : Set.InjOn (fun i : {D : Set X' // Ex.IsGlobalMember D} => (i : Set X') ∩ Ex.W k)
      {i | ((i : Set X') ∩ Ex.W k).Nonempty} := by
    intro i hi j _ hij
    exact Subtype.ext (Ex.globalMember_unique i.2 j.2 k hi hij)
  refine Set.Finite.of_finite_image ?_ hinj
  refine (List.finite_toSet (Ex.B k)).subset ?_
  rintro _ ⟨i, hi, rfl⟩
  exact i.2.mem_of_nonempty Ex k hi

theorem coordinates_globalMember (x : X') :
    ∃ S : {D : Set X' // Ex.IsGlobalMember D} → Finset (Fin n),
      IsCoordinateFamilyAt n (fun i : {D : Set X' // Ex.IsGlobalMember D} => (i : Set X')) S x ∧
        (∀ i : {D : Set X' // Ex.IsGlobalMember D}, x ∈ (i : Set X') → (S i).card = 1) ∧
        Set.InjOn S {i : {D : Set X' // Ex.IsGlobalMember D} | x ∈ (i : Set X')} := by
  obtain ⟨k, hk⟩ := Ex.cover x
  obtain ⟨S, ⟨Φ, hsrc, hzero, hcoord⟩, hcard, hinj⟩ := (Ex.snc k).2 ⟨x, hk⟩
  have hpos : ∀ i : {D : Set X' // Ex.IsGlobalMember D}, ((i : Set X') ∩ Ex.W k) ∈ Ex.B k →
      ∃ p : Fin ((Ex.B k).map ((Subtype.val : Ex.W k → X') ⁻¹' ·)).length,
        ((Ex.B k).map ((Subtype.val : Ex.W k → X') ⁻¹' ·)).get p =
          (Subtype.val : Ex.W k → X') ⁻¹' (i : Set X') := fun i hi => by
    obtain ⟨p, hp⟩ := List.mem_iff_get.mp (List.mem_map_of_mem (f := ((Subtype.val : Ex.W k → X') ⁻¹' ·)) hi)
    refine ⟨p, hp.trans ?_⟩
    ext q
    exact ⟨fun h => h.1, fun h => ⟨h, q.2⟩⟩
  let S' : {D : Set X' // Ex.IsGlobalMember D} → Finset (Fin n) := fun i =>
    if hi : ((i : Set X') ∩ Ex.W k) ∈ Ex.B k then S (hpos i hi).choose else ∅
  have hmemx : ∀ i : {D : Set X' // Ex.IsGlobalMember D}, x ∈ (i : Set X') → ((i : Set X') ∩ Ex.W k) ∈ Ex.B k :=
    fun i hx => i.2.mem_of_nonempty Ex k ⟨x, hx, hk⟩
  have hS' : ∀ (i : {D : Set X' // Ex.IsGlobalMember D}) (hx : x ∈ (i : Set X')),
      S' i = S (hpos i (hmemx i hx)).choose := fun i hx => dif_pos (hmemx i hx)
  have hget : ∀ (i : {D : Set X' // Ex.IsGlobalMember D}) (hx : x ∈ (i : Set X')),
      ((Ex.B k).map ((Subtype.val : Ex.W k → X') ⁻¹' ·)).get (hpos i (hmemx i hx)).choose =
        (Subtype.val : Ex.W k → X') ⁻¹' (i : Set X') := fun i hx => (hpos i (hmemx i hx)).choose_spec
  refine ⟨S', ?_, ?_, ?_⟩
  · apply (NormalCrossingsInvariance.isCoordinateFamilyAt_preimage_val_iff (x := (⟨x, hk⟩ : Ex.W k))).mp
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
    have hE : (Subtype.val : Ex.W k → X') ⁻¹' (i : Set X') = (Subtype.val : Ex.W k → X') ⁻¹' (j : Set X') := by
      rw [← hget i hi', ← hget j hj', hp]
    have hinter : (i : Set X') ∩ Ex.W k = (j : Set X') ∩ Ex.W k := by
      ext y
      constructor
      · rintro ⟨hy, hyV⟩
        have hy' : (⟨y, hyV⟩ : Ex.W k) ∈ (Subtype.val : Ex.W k → X') ⁻¹' (j : Set X') := hE ▸ hy
        exact ⟨hy', hyV⟩
      · rintro ⟨hy, hyV⟩
        have hy' : (⟨y, hyV⟩ : Ex.W k) ∈ (Subtype.val : Ex.W k → X') ⁻¹' (i : Set X') := hE.symm ▸ hy
        exact ⟨hy', hyV⟩
    exact Subtype.ext (Ex.globalMember_unique i.2 j.2 k ⟨x, hi', hk⟩ hinter)

/-- **Global simple normal crossings from a compatible exhaustion.** -/
theorem exists_isLocallyFiniteSNCDivisor :
    ∃ (ι : Type u) (D : ι → Set X'), HironakaActualLocallyFiniteBoundary.IsLocallyFiniteSNCDivisor n D ∧
      (∀ i, (D i).Nonempty) ∧ (⋃ i, D i) = ⋃ k, ⋃ H ∈ Ex.B k, H :=
  ⟨{D : Set X' // Ex.IsGlobalMember D}, fun i => i.1,
    ⟨Ex.locallyFinite_globalMember, fun i => Ex.isClosed_globalMember i.2, Ex.coordinates_globalMember⟩,
    fun i => i.2.1, Ex.iUnion_globalMember⟩

end SNCExhaustion

/-! ### The boundary of a glued embedded resolution -/

section Embedded

open HironakaG3REmbeddedBoundary HironakaG3RChartOfMember

variable {X : CMfd.{u} n} {V : ClosedIrreducibleAnalyticSubvariety n X} {X' : CMfd.{u} n} {P : X' → X}

theorem chartBoundary_subset_V (c : TowerChart (embeddedClass V) X' P) {H : Set X'} (hH : H ∈ chartBoundary c) :
    H ⊆ c.V := by
  obtain ⟨K, -, rfl⟩ := List.mem_map.mp hH
  rintro _ ⟨y, -, rfl⟩
  exact (c.φ y).2

/-- **Global simple normal crossings of the boundary of a glued embedded resolution**: `Exc P` is the union of a locally
finite indexed simple normal crossings family of nonempty closed sets. -/
theorem exists_isLocallyFiniteSNCDivisor_exceptionalLocus (hV : V.dim < n) (h : IsGluedEmbeddedResolution V X' P) :
    ∃ (ι : Type u) (D : ι → Set X'), HironakaActualLocallyFiniteBoundary.IsLocallyFiniteSNCDivisor n D ∧
      (∀ i, (D i).Nonempty) ∧ (⋃ i, D i) = exceptionalLocus n P := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  let K := CompactExhaustion.choice X
  have hU : ∀ k : ℕ, ∃ c : TowerChart (embeddedClass V) X' P, c.U = ⟨interior (K (k + 1)), isOpen_interior⟩ :=
    fun k => exists_embeddedChart_of_subset_isCompact hV h _ (K.isCompact (k + 1)) interior_subset
  choose c hc using hU
  have hUmono : ∀ {j k : ℕ}, j ≤ k → (c j).U ≤ (c k).U := fun {j k} hjk => by
    rw [hc, hc]
    exact interior_mono (K.subset (by omega))
  have hVmono : ∀ {j k : ℕ}, j ≤ k → ((c j).V : Set X') ⊆ (c k).V := fun {j k} hjk y hy => by
    have h' : y ∈ ((c j).V : Set X') := hy
    rw [(c j).V_eq] at h'
    exact (c k).mem_V (hUmono hjk h')
  have hcover : ∀ y : X', ∃ k, y ∈ (c k).V := fun y => by
    obtain ⟨k, hk⟩ := K.exists_mem (P y)
    refine ⟨k, (c k).mem_V ?_⟩
    rw [hc]
    exact K.subset_interior_succ k hk
  have hnested : ∀ {j k : ℕ}, j ≤ k →
      ((chartBoundary (c k)).map (· ∩ ((c j).V : Set X'))).filter (fun H => decide H.Nonempty) =
        (chartBoundary (c j)).filter (fun H => decide H.Nonempty) := fun {j k} hjk => by
    have hov := chartBoundary_overlap hV (c j) (c k)
    have hpre : P ⁻¹' (((c j).U ⊓ (c k).U : Opens X) : Set X) = ((c j).V : Set X') := by
      rw [(c j).V_eq]
      ext y
      exact ⟨fun h => h.1, fun h => ⟨h, hUmono hjk h⟩⟩
    rw [hpre] at hov
    have hself : (chartBoundary (c j)).map (· ∩ ((c j).V : Set X')) = chartBoundary (c j) := by
      conv_rhs => rw [← List.map_id (chartBoundary (c j))]
      exact List.map_congr_left fun H hH => inter_eq_left.mpr (chartBoundary_subset_V (c j) hH)
    rw [hself] at hov
    exact hov.symm
  let Ex : SNCExhaustion X' :=
    { W := fun k => (c k).V
      B := fun k => chartBoundary (c k)
      mono := hVmono
      cover := hcover
      sub := fun {k} {H} hH => chartBoundary_subset_V (c k) hH
      snc := fun k => (chart_boundary hV h (c k)).1
      nested := hnested }
  obtain ⟨ι, D, hD, hne, hDU⟩ := Ex.exists_isLocallyFiniteSNCDivisor
  refine ⟨ι, D, hD, hne, hDU.trans ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk'⟩ := mem_iUnion.mp hy
    obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hk'
    have hy' : y ∈ ⋃ H ∈ chartBoundary (c k), H := mem_biUnion hH hyH
    rw [(chart_boundary hV h (c k)).2.1] at hy'
    exact hy'.1
  · intro hy
    obtain ⟨k, hk⟩ := hcover y
    have hy' : y ∈ ⋃ H ∈ chartBoundary (c k), H := by
      rw [(chart_boundary hV h (c k)).2.1]
      exact ⟨hy, hk⟩
    obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hy'
    exact mem_iUnion.mpr ⟨k, mem_iUnion₂.mpr ⟨H, hH, hyH⟩⟩

end Embedded

end

end Hironaka.HironakaG3REmbeddedGlobalSNC
