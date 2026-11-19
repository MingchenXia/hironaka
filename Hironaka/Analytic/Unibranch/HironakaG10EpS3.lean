import Hironaka.Analytic.Unibranch.HironakaG10RdMacroStep
import Hironaka.Analytic.Unibranch.HironakaG10MwStepProperImage
import Hironaka.Analytic.Unibranch.HironakaG10EpStrictAnalytic

/-!
# S3: "i is not affected by Π₁" (Hironaka p. 544; plan item L2 of lane G10RD)

Run 0081 lane G10EP.  Blueprint: `hironaka-g10ep-s3.tex`.

Let `R` be an (F)-datum with index `i = topIndexOf R` and selected set `C_i = csetOf R`, and let `Π₁` be a
permissible run of `R̄ = R.withB C_i` after which the family is flat over the strict transform of `C_i`.
Read as a run of `R` (same centres), `Π₁` does not change the index, and the family is flat over the new
selected set (`s3_of_strata`; in the exact shape of the hypothesis `hS3` of
`HironakaG10RdMacroStep.macroStep_of_S3_Dβ`: `hS3_of_stratification`).

Proof, one step at a time (`badIdx_next`, `cset_next_subset`).  Every centre lies in `s₁(f/C̄)` and, by
Lemma 4.5.1 (2) at the start and L5 (a) along the run, misses every tracked support; so the tracked supports
are transported by inverse image, and near them the step is an isomorphism.  By L5 (c) (lane G10MW), the
stratum components of the strict transform of `B` not inside the exceptional set are the strict transforms
of the stratum components of `B` not inside the centre; a component meeting a tracked support is of this
kind.  Meeting a tracked support off the next stratum and relative openness along a tracked support are
read through the local isomorphism.  Hence the bad components correspond index by index (same index set,
same `topIndexOf`), and every selected component of the new datum is the strict transform of a selected
component of the old one, so the new selected set lies in the strict transform of the old one, over which
the family is flat at the end of the run.

The stratification contract enters only through the analyticity of the strata of `B` and the strict
decrease of nonempty strata (needed for Lemma 4.5.1 at the start); no named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10EpS3

open Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex
  Hironaka.Analytic.Unibranch.HironakaG10RdMacroStep
  Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep
  Hironaka.Analytic.Unibranch.HironakaG10MwStrataStep
  Hironaka.Analytic.Unibranch.HironakaG10MwStepProperImage
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-! ### The index depends only on the set of bad indices -/

/-- The set of indices of the bad components of an (F)-datum. -/
def badIdx {s : Stage} {q : ℕ} (R : FDatum s q) : Set ℕ :=
  {j | ∃ C, (j, C) ∈ badComponents s.f R.B (fun p => (R.Z p).support)}

theorem bound_iff {s : Stage} {q : ℕ} (R : FDatum s q) (i : ℕ) :
    (∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ i) ↔ ∀ j ∈ badIdx R, j ≤ i := by
  constructor
  · rintro hi j ⟨C, hC⟩
    exact hi (j, C) hC
  · intro hi jC hjC
    exact hi jC.1 ⟨jC.2, hjC⟩

/-- Data with the same bad indices have the same index. -/
theorem topIndexOf_eq_of_badIdx {s s' : Stage} {q : ℕ} {R : FDatum s q} {R' : FDatum s' q}
    (h : badIdx R' = badIdx R) : topIndexOf R' = topIndexOf R := by
  classical
  unfold topIndexOf
  by_cases hR : ∃ i, ∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ i
  · have hR' : ∃ i, ∀ jC ∈ badComponents s'.f R'.B (fun p => (R'.Z p).support), jC.1 ≤ i := by
      obtain ⟨i, hi⟩ := hR
      exact ⟨i, (bound_iff R' i).mpr (h ▸ (bound_iff R i).mp hi)⟩
    rw [dif_pos hR, dif_pos hR']
    apply le_antisymm
    · exact topIndex_le hR' ((bound_iff R' _).mpr (h ▸ (bound_iff R _).mp (le_topIndex hR)))
    · exact topIndex_le hR ((bound_iff R _).mpr (h.symm ▸ (bound_iff R' _).mp (le_topIndex hR')))
  · have hR' : ¬ ∃ i, ∀ jC ∈ badComponents s'.f R'.B (fun p => (R'.Z p).support), jC.1 ≤ i := by
      rintro ⟨i, hi⟩
      exact hR ⟨i, (bound_iff R i).mpr (h.symm ▸ (bound_iff R' i).mp hi)⟩
    rw [dif_neg hR, dif_neg hR']

/-! ### One step: transfer of components, meeting and relative openness -/

section Step

variable (s : Stage) (c : AdmissibleCentre s.f)

/-- The step is an open map on the complement of the exceptional set. -/
theorem isOpen_image_of_subset_compl {W : Set (nextWith s c).X.obj.left} (hW : IsOpen W)
    (hWE : W ⊆ σb s c ⁻¹' (nonunitLocus c.B c.b)ᶜ) : IsOpen (σb s c '' W) := by
  obtain ⟨V, j, hj, hjr, hjσ, -⟩ := isIsoOver_stepσ s c
  have hWj : W ⊆ range j.base := by
    rw [hjr]
    exact hWE
  have himg : σb s c '' W = (j ≫ (stepσ s c).hom.left).base '' (j.base ⁻¹' W) := by
    rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, image_comp,
      image_preimage_eq_of_subset hWj]
  rw [himg]
  exact hjσ.base_open.isOpenMap _ (hW.preimage j.base.hom.continuous)

variable {s c}

/-- **Meeting a tracked set off the next stratum transfers through the step** (forward). -/
theorem meets_of_next {B : Set s.X.obj.left} (hB : IsClosed B) {T : Set s.X.obj.left}
    (hDT : nonunitLocus c.B c.b ∩ T = ∅) {C : Set s.X.obj.left} (hC : IsClosed C) (j : ℕ)
    (h : ((strictSet s c C \ strata (nextWith s c).f (strictSet s c B) (j + 1)) ∩
      σb s c ⁻¹' T).Nonempty) :
    ((C \ strata s.f B (j + 1)) ∩ T).Nonempty := by
  obtain ⟨x', ⟨hx'C, hx'S⟩, hx'T⟩ := h
  have hxD : σb s c x' ∉ nonunitLocus c.B c.b := fun hD => (eq_empty_iff_forall_notMem.mp hDT) _ ⟨hD, hx'T⟩
  refine ⟨σb s c x', ⟨strictSet_subset_preimage s c hC hx'C, ?_⟩, hx'T⟩
  exact fun hS => hx'S ((mem_strata_next_iff s c hB (j + 1) x' hxD).mpr hS)

/-- **Meeting a tracked set off the next stratum transfers through the step** (backward). -/
theorem next_meets {B : Set s.X.obj.left} (hB : IsClosed B) {T : Set s.X.obj.left}
    (hDT : nonunitLocus c.B c.b ∩ T = ∅) {C : Set s.X.obj.left} (j : ℕ)
    (h : ((C \ strata s.f B (j + 1)) ∩ T).Nonempty) :
    ((strictSet s c C \ strata (nextWith s c).f (strictSet s c B) (j + 1)) ∩
      σb s c ⁻¹' T).Nonempty := by
  obtain ⟨z, ⟨hzC, hzS⟩, hzT⟩ := h
  have hzD : z ∉ nonunitLocus c.B c.b := fun hD => (eq_empty_iff_forall_notMem.mp hDT) _ ⟨hD, hzT⟩
  obtain ⟨z', rfl⟩ := compl_subset_range s c hzD
  refine ⟨z', ⟨subset_closure ⟨hzC, hzD⟩, ?_⟩, hzT⟩
  exact fun hS => hzS ((mem_strata_next_iff s c hB (j + 1) z' hzD).mp hS)

/-- Relative openness along a tracked set passes to the strict transform. -/
theorem isRelOpen_strictSet {T : Set s.X.obj.left} {C : Set s.X.obj.left} (hC : IsClosed C)
    (h : IsRelOpen C T) : IsRelOpen (strictSet s c C) (σb s c ⁻¹' T) := by
  obtain ⟨U, hU, hCU⟩ := h
  refine ⟨σb s c ⁻¹' U, hU.preimage (continuous_σb s c), ?_⟩
  ext x'
  constructor
  · rintro ⟨hx'C, hx'T⟩
    have hx : σb s c x' ∈ C ∩ T := ⟨strictSet_subset_preimage s c hC hx'C, hx'T⟩
    rw [hCU] at hx
    exact ⟨hx'C, hx.2⟩
  · rintro ⟨hx'C, hx'U⟩
    have hx : σb s c x' ∈ C ∩ U := ⟨strictSet_subset_preimage s c hC hx'C, hx'U⟩
    rw [← hCU] at hx
    exact ⟨hx'C, hx.2⟩

/-- Relative openness along a tracked set missing the centre descends from the strict transform. -/
theorem isRelOpen_of_strictSet {T : Set s.X.obj.left} (hDT : nonunitLocus c.B c.b ∩ T = ∅)
    {C : Set s.X.obj.left} (h : IsRelOpen (strictSet s c C) (σb s c ⁻¹' T)) : IsRelOpen C T := by
  obtain ⟨U', hU', hCU'⟩ := h
  let W := U' ∩ σb s c ⁻¹' (nonunitLocus c.B c.b)ᶜ
  refine ⟨σb s c '' W, isOpen_image_of_subset_compl s c (hU'.inter (isOpen_preimage_compl s c))
    inter_subset_right, ?_⟩
  ext z
  constructor
  · rintro ⟨hzC, hzT⟩
    have hzD : z ∉ nonunitLocus c.B c.b := fun hD => (eq_empty_iff_forall_notMem.mp hDT) _ ⟨hD, hzT⟩
    obtain ⟨z', rfl⟩ := compl_subset_range s c hzD
    have hz' : z' ∈ strictSet s c C ∩ σb s c ⁻¹' T := ⟨subset_closure ⟨hzC, hzD⟩, hzT⟩
    rw [hCU'] at hz'
    exact ⟨hzC, z', ⟨hz'.2, hzD⟩, rfl⟩
  · rintro ⟨hzC, z', ⟨hz'U, hz'D⟩, rfl⟩
    have hz' : z' ∈ strictSet s c C ∩ U' := ⟨subset_closure ⟨hzC, hz'D⟩, hz'U⟩
    rw [← hCU'] at hz'
    exact ⟨hzC, hz'.2⟩

variable (hf : IsProperMap s.f.hom.left.base)
include hf

/-- **The bad indices do not change under a step whose centre misses the tracked supports.** -/
theorem badIdx_next {B : Set s.X.obj.left} (hB : IsClosed B) {q : ℕ} (T T' : Fin q → Set s.X.obj.left)
    (hT : T = T') (hDT : ∀ p, nonunitLocus c.B c.b ∩ T p = ∅)
    (T₁ : Fin q → Set (nextWith s c).X.obj.left) (hT₁ : ∀ p, T₁ p = σb s c ⁻¹' T' p) :
    {j | ∃ C, (j, C) ∈ badComponents (nextWith s c).f (strictSet s c B) T₁} =
      {j | ∃ C, (j, C) ∈ badComponents s.f B T} := by
  subst hT
  have hDa := HironakaG10EpStrictAnalytic.isAnalyticSubset_centre_nonunitLocus c
  ext j
  constructor
  · rintro ⟨C', hj1, hC', ⟨p₀, hmeet⟩, ⟨p₁, hnrel⟩⟩
    rw [hT₁] at hmeet hnrel
    have hCE : ¬ C' ⊆ σb s c ⁻¹' nonunitLocus c.B c.b := by
      intro hsub
      obtain ⟨x', ⟨hx'C, -⟩, hx'T⟩ := hmeet
      exact (eq_empty_iff_forall_notMem.mp (hDT p₀)) _ ⟨hsub hx'C, hx'T⟩
    obtain ⟨C, hC, -, rfl⟩ := exists_isStratumComponent_of_next_proper s c hf hB hDa j hC' hCE
    have hCc : IsClosed C := hC.1.1.isClosed
    exact ⟨C, hj1, hC, ⟨p₀, meets_of_next hB (hDT p₀) hCc j hmeet⟩,
      ⟨p₁, fun hrel => hnrel (isRelOpen_strictSet hCc hrel)⟩⟩
  · rintro ⟨C, hj1, hC, ⟨p₀, hmeet⟩, ⟨p₁, hnrel⟩⟩
    have hCD : ¬ C ⊆ nonunitLocus c.B c.b := by
      intro hsub
      obtain ⟨z, ⟨hzC, -⟩, hzT⟩ := hmeet
      exact (eq_empty_iff_forall_notMem.mp (hDT p₀)) _ ⟨hsub hzC, hzT⟩
    obtain ⟨hC', -⟩ := isStratumComponent_strictSet_proper s c hf hB hDa j hC hCD
    refine ⟨strictSet s c C, hj1, hC', ⟨p₀, ?_⟩, ⟨p₁, ?_⟩⟩
    · rw [hT₁]
      exact next_meets hB (hDT p₀) j hmeet
    · rw [hT₁]
      exact fun hrel => hnrel (isRelOpen_of_strictSet (hDT p₁) hrel)

/-- **Every selected component of the new datum is the strict transform of a selected component of the
old one.** -/
theorem cset_next_subset {B : Set s.X.obj.left} (hB : IsClosed B) {q : ℕ} (T : Fin q → Set s.X.obj.left)
    (hDT : ∀ p, nonunitLocus c.B c.b ∩ T p = ∅)
    (T₁ : Fin q → Set (nextWith s c).X.obj.left) (hT₁ : ∀ p, T₁ p = σb s c ⁻¹' T p) (i : ℕ) :
    Cset (nextWith s c).f (strictSet s c B) T₁ i ⊆ strictSet s c (Cset s.f B T i) := by
  have hDa := HironakaG10EpStrictAnalytic.isAnalyticSubset_centre_nonunitLocus c
  intro x' hx'
  simp only [Cset, mem_iUnion] at hx'
  obtain ⟨⟨j, C'⟩, ⟨hij, hC', p₀, hmeet⟩, hx'C'⟩ := hx'
  rw [hT₁] at hmeet
  have hCE : ¬ C' ⊆ σb s c ⁻¹' nonunitLocus c.B c.b := by
    intro hsub
    obtain ⟨y', ⟨hy'C, -⟩, hy'T⟩ := hmeet
    exact (eq_empty_iff_forall_notMem.mp (hDT p₀)) _ ⟨hsub hy'C, hy'T⟩
  obtain ⟨C, hC, -, rfl⟩ := exists_isStratumComponent_of_next_proper s c hf hB hDa j hC' hCE
  have hsel : (j, C) ∈ selectedHigherComponents s.f B T i :=
    ⟨hij, hC, p₀, meets_of_next hB (hDT p₀) hC.1.1.isClosed j hmeet⟩
  refine strictSet_mono s c ?_ hx'C'
  intro z hz
  simp only [Cset, mem_iUnion]
  exact ⟨(j, C), hsel, hz⟩

end Step

/-! ### Transported supports of a step missing them -/

theorem trackedTransport_Z_eq_preimage {s : Stage} {q : ℕ} (R : FDatum s q) (c : AdmissibleCentre s.f)
    (p : Fin q) (hdisj : nonunitLocus c.B c.b ∩ (R.Z p).support = ∅) :
    (R.trackedTransport c).Z p = σb s c ⁻¹' (R.Z p).support := by
  let _ := c.finiteType
  ext x'
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact HironakaG10ChowTrackedDatum.mem_transport_of_not_mem_nonunitLocus c.B c.b c.dense s.f
      R.tracked p x' hx (fun hD => (eq_empty_iff_forall_notMem.mp hdisj) _ ⟨hD, hx⟩)

/-! ### Along the run -/

/-- **S3 along a run** (induction on the run of `R'`, read as a run of `R`). -/
theorem s3_run {q : ℕ} : ∀ {s : Stage} {R' : FDatum s q} (l : PermRun s R') (R : FDatum s q)
    (hZ : R'.Z = R.Z) (hB : R'.B ⊆ R.B) (i : ℕ), IsProperMap s.f.hom.left.base →
    (∀ p, relNonflat s.f R'.B ∩ (R.Z p).support = ∅) →
    Cset s.f R.B (fun p => (R.Z p).support) i ⊆ R'.B → FlatOverB l.final.2 →
    badIdx (l.liftB R hZ hB).final.2 = badIdx R ∧
      relNonflat (l.liftB R hZ hB).final.1.f
        (Cset (l.liftB R hZ hB).final.1.f (l.liftB R hZ hB).final.2.B
          (fun p => ((l.liftB R hZ hB).final.2.Z p).support) i) = ∅
  | s, R', .nil _ _, R, hZ, hB, i, hf, hI, hCs, hflat => by
    refine ⟨rfl, ?_⟩
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := relNonflat_mono s.f hCs hx
    have hflat' : relNonflat s.f R'.B = ∅ := hflat
    rw [hflat'] at hx'
    exact hx'
  | s, R', .cons _ _ st rest, R, hZ, hB, i, hf, hI, hCs, hflat => by
    have hDT : ∀ p, nonunitLocus st.c.B st.c.b ∩ (R.Z p).support = ∅ := fun p =>
      eq_empty_of_subset_empty (fun x hx => (hI p).subset ⟨st.sub hx.1, hx.2⟩)
    have hsupp : ∀ p, (st.next.Z p).support = σb s st.c ⁻¹' (R.Z p).support := by
      intro p
      rw [st.next_support p, trackedTransport_Z_eq_preimage R' st.c p (by rw [hZ]; exact hDT p),
        hZ]
    have hB₁ : st.next.B ⊆ strictSet s st.c R.B := by
      rw [st.next_B]
      exact strictSet_mono s st.c hB
    have hf₁ : IsProperMap (nextWith s st.c).f.hom.left.base := isProperMap_next s st.c hf
    have hI₁ : ∀ p, relNonflat (nextWith s st.c).f st.next.B ∩ (st.next.Z p).support = ∅ := by
      intro p
      apply eq_empty_iff_forall_notMem.mpr
      rintro x' ⟨hx'N, hx'Z⟩
      rw [hsupp p] at hx'Z
      have hxD : σb s st.c x' ∉ nonunitLocus st.c.B st.c.b := fun hD =>
        (eq_empty_iff_forall_notMem.mp (hDT p)) _ ⟨hD, hx'Z⟩
      rw [st.next_B] at hx'N
      have h1 : σb s st.c x' ∈ relNonflat s.f R'.B :=
        (mem_strata_next_iff s st.c R'.closed 1 x' hxD).mp hx'N
      exact (eq_empty_iff_forall_notMem.mp (hI p)) _ ⟨h1, hx'Z⟩
    have hCs₁ : Cset (nextWith s st.c).f (strictSet s st.c R.B)
        (fun p => (st.next.Z p).support) i ⊆ st.next.B := by
      rw [st.next_B]
      exact (cset_next_subset hf R.closed (fun p => (R.Z p).support) hDT _ hsupp i).trans
        (strictSet_mono s st.c hCs)
    obtain ⟨h1, h2⟩ := s3_run rest (st.liftB R hZ hB).next rfl hB₁ i hf₁ hI₁ hCs₁ hflat
    refine ⟨h1.trans ?_, h2⟩
    exact badIdx_next hf R.closed _ _ rfl hDT _ hsupp

/-! ### S3 -/

/-- **S3** (Hironaka p. 544, "i is not affected by Π₁"): for an (F)-datum on a compact base with proper
family, analytic strata strictly decreasing while nonempty, and a permissible run of `R̄ = R.withB C_i`
after which the family is flat, the run read for `R` keeps the index and the family is flat over the new
selected set. -/
theorem s3_of_strata {s : Stage} {q : ℕ} (R : FDatum s q) (hc : CompactSpace s.X.obj.left)
    (hp : IsProperMap s.f.hom.left.base) (hA : ∀ j, s.X.IsAnalyticSubset (strata s.f R.B j))
    (hproper : ∀ n, (strata s.f R.B n).Nonempty → strata s.f R.B (n + 1) ≠ strata s.f R.B n)
    (hC : IsClosed (csetOf R)) (l : PermRun s (R.withB (csetOf R) hC)) (hl : FlatOverB l.final.2) :
    topIndexOf (liftRun R hC l).final.2 = topIndexOf R ∧
      relNonflat (liftRun R hC l).final.1.f (csetOf (liftRun R hC l).final.2) = ∅ := by
  have := hc
  obtain ⟨h⟩ : Nonempty (∃ i, ∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ i) :=
    ⟨exists_topIndex_bound (f := s.f) (B := R.B) (Z := fun p => (R.Z p).support) hA hproper⟩
  have htop : topIndexOf R = topIndex s.f R.B (fun p => (R.Z p).support) h := by
    unfold topIndexOf
    rw [dif_pos h]
  have hI : ∀ p, relNonflat s.f (csetOf R) ∩ (R.Z p).support = ∅ := by
    have h451 := (lemma_4_5_1_at_topIndex (f := s.f) (B := R.B) R.Z hA hproper h).2.2.2.2
    intro p
    have := h451 p
    rw [← htop] at this
    exact this
  obtain ⟨hbad, hrel⟩ := s3_run l R rfl (cset_subset_B R _) (topIndexOf R) hp hI subset_rfl hl
  have hidx : topIndexOf (liftRun R hC l).final.2 = topIndexOf R := topIndexOf_eq_of_badIdx hbad
  refine ⟨hidx, ?_⟩
  change relNonflat (liftRun R hC l).final.1.f
    (Cset (liftRun R hC l).final.1.f (liftRun R hC l).final.2.B
      (fun p => ((liftRun R hC l).final.2.Z p).support) (topIndexOf (liftRun R hC l).final.2)) = ∅
  rw [hidx]
  exact hrel

/-- **`hS3` of `HironakaG10RdMacroStep.macroStep_of_S3_Dβ`**, from the stratification contract on compact
bases with proper families (`hF1`: relative non-flat sets of analytic sets are analytic; `hF2`: they are
nowhere dense in them) and analyticity of the sets satisfying `dim`. -/
theorem hS3_of_stratification (dim : ℕ → ∀ s : Stage, Set s.X.obj.left → Prop)
    (hF1 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A))
    (hF2 : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))
    (hdimA : ∀ (n : ℕ) (s : Stage) (B : Set s.X.obj.left), dim n s B → s.X.IsAnalyticSubset B)
    (hC : ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B → IsClosed (csetOf R)) :
    ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q) (hc : CompactSpace s.X.obj.left)
      (hp : IsProperMap s.f.hom.left.base) (hd : dim (n + 1) s R.B)
      (l : PermRun s (R.withB (csetOf R) (hC n s q R hc hp hd))), FlatOverB l.final.2 →
        topIndexOf (liftRun R _ l).final.2 = topIndexOf R ∧
          relNonflat (liftRun R _ l).final.1.f (csetOf (liftRun R _ l).final.2) = ∅ := by
  intro n s q R hc hp hd l hl
  have hA : ∀ j, s.X.IsAnalyticSubset (strata s.f R.B j) := by
    intro j
    induction j with
    | zero => exact hdimA (n + 1) s R.B hd
    | succ j ih => exact hF1 s hc hp _ ih
  have hproper : ∀ m, (strata s.f R.B m).Nonempty →
      strata s.f R.B (m + 1) ≠ strata s.f R.B m := by
    intro m hne heq
    have hsub := hF2 s hc hp _ (hA m)
    have heq' : relNonflat s.f (strata s.f R.B m) = strata s.f R.B m := heq
    rw [heq', sdiff_self, closure_empty] at hsub
    obtain ⟨x, hx⟩ := hne
    exact hsub hx
  exact s3_of_strata R hc hp hA hproper _ l hl

end

end Hironaka.Analytic.Unibranch.HironakaG10EpS3
