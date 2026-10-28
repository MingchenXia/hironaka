import TranscendentalNakamaye.Pending.HironakaLocallyFiniteResolutionSequence
import TranscendentalNakamaye.Pending.HironakaOriginalOldBranchEmptyProjection
import TranscendentalNakamaye.Pending.HironakaTerminalAtlasHolomorphic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# The actual geometric limit of a given locally finite blowup history

The input is an actual `GrowingSeq` and local finiteness of its indexed closed
centre footprints on the original base.  Every empty step remains in that
history.  The limit is the actual compatible-thread subspace of the product
of the recorded stages, equipped with its product subspace topology BEFORE
the complex atlas is constructed.  Stable finite tails internally produce
the saturated open embeddings, their holomorphic overlaps, all proper
holomorphic stage projections, and the universal compatible cone.

This is only the geometric GIVEN-LF construction.  No terminality, native
ideal or boundary gluing, internally scheduled local finiteness, countable
phase concatenation, or closure of the original G3 problem is asserted.

Blueprint: `hironaka-actual-locally-finite-blowup-limit-geometry-extension.tex`.
Original failed784 and historical candidate813 are preserved separately in
`work/g3-given-lf-geometry-repair-20261025`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Topology Function IsManifold
open scoped Topology Manifold ContDiff

universe u v

namespace TranscendentalNakamaye.Pending.HironakaActualLocallyFiniteBlowupLimitGeometry

noncomputable section

open FirstPass FirstPass.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  RestrictEmptyTower HironakaTerminalAtlasTopology HironakaTerminalAtlasHolomorphic

variable {n : ℕ} {X : CMfd.{u} n}

/-! ## The actual adjacent maps and finite tails -/

def actualStepMap (s : GrowingSeq X) (i : ℕ) : (s.stage (i + 1)).1 → (s.stage i).1 :=
  (exists_step_map s i).choose

theorem actualStepMap_isBlowup (s : GrowingSeq X) (i : ℕ) :
    IsBlowupAlong n (stepCentre s i) (actualStepMap s i) :=
  (exists_step_map s i).choose_spec.choose

theorem actual_stage_succ (s : GrowingSeq X) (i : ℕ) :
    (s.stage (i + 1)).2 = .step (s.stage i).2 (stepCentre s i)
      (actualStepMap s i) (actualStepMap_isBlowup s i) :=
  (exists_step_map s i).choose_spec.choose_spec

/-- A two-index reindexing of the actual finite tail, retaining every step. -/
def actualTail (s : GrowingSeq X) (j i : ℕ) (h : j ≤ i) :
    BlowupTower (s.stage j).1 (s.stage i).1 :=
  Nat.leRecOn (C := fun k => BlowupTower (s.stage j).1 (s.stage k).1) h
    (fun {k} T => .step T (stepCentre s k) (actualStepMap s k) (actualStepMap_isBlowup s k))
    .refl

@[simp] theorem actualTail_self (s : GrowingSeq X) (j : ℕ) :
    actualTail s j j le_rfl = .refl := Nat.leRecOn_self _

theorem actualTail_succ (s : GrowingSeq X) {j i : ℕ} (h : j ≤ i) :
    actualTail s j (i + 1) (by omega) = .step (actualTail s j i h)
      (stepCentre s i) (actualStepMap s i) (actualStepMap_isBlowup s i) :=
  Nat.leRecOn_succ h _

/-- This adapter is the existing actual tail, rather than a new history. -/
theorem actualTail_eq_existing (s : GrowingSeq X) (j k : ℕ) :
    actualTail s j (j + k) (by omega) =
      HironakaLocallyFiniteResolutionSequence.tailTower s j k := by
  induction k with
  | zero => simp [HironakaLocallyFiniteResolutionSequence.tailTower]
  | succ k ih =>
      calc
        actualTail s j (j + (k + 1)) (by omega) = .step (actualTail s j (j + k) (by omega))
            (stepCentre s (j + k)) (actualStepMap s (j + k)) (actualStepMap_isBlowup s (j + k)) := by
          simpa only [Nat.add_succ] using actualTail_succ (s := s) (j := j) (i := j + k) (by omega)
        _ = HironakaLocallyFiniteResolutionSequence.tailTower s j (k + 1) := by rw [ih]; rfl

theorem actualTail_append_stage (s : GrowingSeq X) {j i : ℕ} (h : j ≤ i) :
    (s.stage j).2.append (actualTail s j i h) = (s.stage i).2 := by
  induction i, h using Nat.le_induction with
  | base => simp
  | succ i h ih =>
      rw [actualTail_succ s h, BlowupTower.append_step, ih, actual_stage_succ]

theorem actualTail_append (s : GrowingSeq X) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (actualTail s i j hij).append (actualTail s j k hjk) =
      actualTail s i k (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k h ih =>
      rw [actualTail_succ s h, BlowupTower.append_step, ih,
        actualTail_succ s (hij.trans h)]

theorem actualTail_proj_comp (s : GrowingSeq X) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (z : (s.stage k).1) :
    (actualTail s i j hij).proj ((actualTail s j k hjk).proj z) =
      (actualTail s i k (hij.trans hjk)).proj z := by
  rw [← actualTail_append s hij hjk, BlowupTower.proj_append]
  rfl

theorem actualTail_base (s : GrowingSeq X) {j i : ℕ} (h : j ≤ i) (z : (s.stage i).1) :
    (s.stage j).2.proj ((actualTail s j i h).proj z) = (s.stage i).2.proj z := by
  rw [← actualTail_append_stage s h, BlowupTower.proj_append]
  rfl

theorem actual_step_base (s : GrowingSeq X) (i : ℕ) (z : (s.stage (i + 1)).1) :
    (s.stage i).2.proj (actualStepMap s i z) = (s.stage (i + 1)).2.proj z := by
  rw [actual_stage_succ]
  rfl

/-! ## The genuine increasing stable open cover -/

/-- Complement of the ENTIRE closed indexed tail of actual footprints. -/
def actualStableOpen (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N : ℕ) : Opens X :=
  ⟨(⋃ i : {i : ℕ // N ≤ i}, centreImage s i)ᶜ,
    ((hLF.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun (i : {i : ℕ // N ≤ i}) => by
        simpa only [Function.comp_apply] using isClosed_centreImage s i.val)).isOpen_compl⟩

theorem mem_actualStableOpen (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N : ℕ) (x : X) :
    x ∈ actualStableOpen s hLF N ↔ ∀ i, N ≤ i → x ∉ centreImage s i := by
  change (x ∉ ⋃ i : {i : ℕ // N ≤ i}, centreImage s i) ↔ _
  simp only [mem_iUnion, not_exists]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.property⟩

theorem actualStableOpen_mono (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    Monotone (actualStableOpen s hLF) := by
  intro N M hNM x hx
  rw [mem_actualStableOpen] at hx ⊢
  exact fun i hi => hx i (hNM.trans hi)

theorem exists_compact_subset_actualStableOpen (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) {K : Set X} (hK : IsCompact K) :
    ∃ N, K ⊆ actualStableOpen s hLF N := by
  obtain ⟨B, hB⟩ := (hLF.finite_nonempty_inter_compact hK).bddAbove
  refine ⟨B + 1, fun x hx => (mem_actualStableOpen s hLF (B + 1) x).mpr ?_⟩
  intro i hi hxi
  have hle : i ≤ B := hB ⟨x, hxi, hx⟩
  omega

theorem actualStableOpen_cover (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (x : X) : ∃ N, x ∈ actualStableOpen s hLF N := by
  obtain ⟨N, hN⟩ := exists_compact_subset_actualStableOpen s hLF
    (K := {x}) isCompact_singleton
  exact ⟨N, hN (mem_singleton x)⟩

def actualStableStageOpen (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N i : ℕ) : Opens (s.stage i).1 :=
  openPreimage (s.stage i).2 (actualStableOpen s hLF N)

private theorem actualTail_openPreimage_eq (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N : ℕ) {j i : ℕ} (h : j ≤ i) :
    actualStableStageOpen s hLF N i =
      openPreimage (actualTail s j i h) (actualStableStageOpen s hLF N j) := by
  apply Opens.ext
  ext z
  change (s.stage i).2.proj z ∈ actualStableOpen s hLF N ↔
    (s.stage j).2.proj ((actualTail s j i h).proj z) ∈ actualStableOpen s hLF N
  rw [actualTail_base]

private theorem actualTail_centresAvoid (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) {N i : ℕ} (hi : N ≤ i) :
    CentresAvoid (actualStableStageOpen s hLF N N) (actualTail s N i hi) := by
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ i hi ih =>
      rw [actualTail_succ s hi, centresAvoid_step_iff]
      refine ⟨ih, disjoint_left.mpr fun z hzC hzU => ?_⟩
      have hz : (s.stage i).2.proj z ∈ actualStableOpen s hLF N := by
        change (s.stage N).2.proj ((actualTail s N i hi).proj z) ∈
          actualStableOpen s hLF N at hzU
        rwa [actualTail_base] at hzU
      exact (mem_actualStableOpen s hLF N _).mp hz i hi ⟨z, hzC, rfl⟩

private def actualOpenEq {A : CMfd.{u} n} (U V : Opens A) (h : U = V) :
    U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V := by
  subst V
  exact Diffeomorph.refl _ _ ∞

private theorem actualOpenEq_val {A : CMfd.{u} n} (U V : Opens A) (h : U = V) (x : U) :
    (actualOpenEq U V h x).val = x.val := by
  subst V
  rfl

private theorem exists_actualStableEquiv (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) {N i : ℕ} (hi : N ≤ i) :
    ∃ E : actualStableStageOpen s hLF N i
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ actualStableStageOpen s hLF N N,
      ∀ z, (E z).val = (actualTail s N i hi).proj z.val := by
  let T := actualTail s N i hi
  let U := actualStableStageOpen s hLF N N
  have he : ResolutionInvariantExt.IsEmptyTower (BlowupTowerTransforms.restrict U T) :=
    (isEmptyTower_restrict_iff U T).mpr (actualTail_centresAvoid s hLF hi)
  obtain ⟨β, hβ⟩ := HironakaOriginalOldBranchEmptyProjection.exists_empty_tower_projection
    (BlowupTowerTransforms.restrict U T) he
  let η := actualOpenEq (actualStableStageOpen s hLF N i) (openPreimage T U)
    (actualTail_openPreimage_eq s hLF N hi)
  refine ⟨η.trans β, fun z => ?_⟩
  change (β (η z)).val = T.proj z.val
  rw [hβ, proj_restrict, actualOpenEq_val]

/-- The inverse is the actual empty-tail section, not a supplied limit chart. -/
def actualStableEquiv (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N i : ℕ) (hi : N ≤ i) :
    actualStableStageOpen s hLF N i
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ actualStableStageOpen s hLF N N :=
  (exists_actualStableEquiv s hLF hi).choose

theorem actualStableEquiv_val (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N i : ℕ) (hi : N ≤ i) (z : actualStableStageOpen s hLF N i) :
    (actualStableEquiv s hLF N i hi z).val = (actualTail s N i hi).proj z.val :=
  (exists_actualStableEquiv s hLF hi).choose_spec z

theorem actualStableEquiv_symm_proj (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N i : ℕ) (hi : N ≤ i)
    (z : actualStableStageOpen s hLF N N) :
    (actualTail s N i hi).proj ((actualStableEquiv s hLF N i hi).symm z).val = z.val := by
  rw [← actualStableEquiv_val, Diffeomorph.apply_symm_apply]

/-! ## The actual compatible-thread carrier and its product subspace topology -/

/-- Compatibility is imposed on the actual recorded adjacent maps. -/
abbrev ActualCompatibleThread (s : GrowingSeq X) :=
  {t : ∀ i : ℕ, (s.stage i).1 // ∀ i, actualStepMap s i (t (i + 1)) = t i}

def actualThreadStageProjection (s : GrowingSeq X) (i : ℕ) :
    ActualCompatibleThread s → (s.stage i).1 := fun t => t.val i

def actualThreadBaseProjection (s : GrowingSeq X) : ActualCompatibleThread s → X :=
  fun t => (s.stage 0).2.proj (t.val 0)

theorem actualThreadStageProjection_continuous (s : GrowingSeq X) (i : ℕ) :
    Continuous (actualThreadStageProjection s i) :=
  (continuous_apply i).comp continuous_subtype_val

theorem actualThreadBaseProjection_continuous (s : GrowingSeq X) :
    Continuous (actualThreadBaseProjection s) :=
  (s.stage 0).2.contMDiff_proj.continuous.comp (actualThreadStageProjection_continuous s 0)

theorem actualThread_down (s : GrowingSeq X) (t : ActualCompatibleThread s)
    {j i : ℕ} (h : j ≤ i) : (actualTail s j i h).proj (t.val i) = t.val j := by
  induction i, h using Nat.le_induction with
  | base => simp
  | succ i h ih =>
      rw [actualTail_succ s h, BlowupTower.proj_step, comp_apply, t.property i, ih]

theorem actualThread_base (s : GrowingSeq X) (t : ActualCompatibleThread s) (i : ℕ) :
    (s.stage i).2.proj (t.val i) = actualThreadBaseProjection s t := by
  rw [← actualTail_base s (Nat.zero_le i) (t.val i), actualThread_down]
  rfl

private def actualStableCoordinate (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N i : ℕ) : actualStableStageOpen s hLF N N → (s.stage i).1 :=
  if hi : i ≤ N then fun z => (actualTail s i N hi).proj z.val
  else fun z => ((actualStableEquiv s hLF N i (by omega)).symm z).val

private theorem actualStableCoordinate_contMDiff (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N i : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualStableCoordinate s hLF N i) := by
  unfold actualStableCoordinate
  split_ifs with hi
  · exact (actualTail s i N hi).contMDiff_proj.comp contMDiff_subtype_val
  · exact contMDiff_subtype_val.comp (actualStableEquiv s hLF N i (by omega)).symm.contMDiff

private theorem actualStableCoordinate_base (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N i : ℕ) (z : actualStableStageOpen s hLF N N) :
    (s.stage i).2.proj (actualStableCoordinate s hLF N i z) = (s.stage N).2.proj z.val := by
  unfold actualStableCoordinate
  split_ifs with hi
  · exact actualTail_base s hi z.val
  · rw [← actualTail_base s (show N ≤ i by omega), actualStableEquiv_symm_proj]

private theorem actualStableCoordinate_down (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N i : ℕ) (hi : N ≤ i)
    (z : actualStableStageOpen s hLF N N) :
    (actualTail s N i hi).proj (actualStableCoordinate s hLF N i z) = z.val := by
  by_cases h : i = N
  · subst i
    simp [actualStableCoordinate]
  · simp only [actualStableCoordinate, dif_neg (show ¬ i ≤ N by omega)]
    exact actualStableEquiv_symm_proj s hLF N i hi z

private theorem actualStableCoordinate_compatible (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N i : ℕ) (z : actualStableStageOpen s hLF N N) :
    actualStepMap s i (actualStableCoordinate s hLF N (i + 1) z) =
      actualStableCoordinate s hLF N i z := by
  by_cases hi : i < N
  · have hnext : i + 1 ≤ N := by omega
    have htail : (actualTail s i N (by omega)).proj =
        actualStepMap s i ∘ (actualTail s (i + 1) N hnext).proj := by
      have ha := actualTail_append s (i := i) (j := i + 1) (k := N) (by omega) hnext
      rw [← ha, BlowupTower.proj_append, actualTail_succ s le_rfl]
      simp
    simp only [actualStableCoordinate, dif_pos hnext, dif_pos (show i ≤ N by omega)]
    exact (congrFun htail z.val).symm
  · have hNi : N ≤ i := by omega
    let a : actualStableStageOpen s hLF N i :=
      ⟨actualStepMap s i (actualStableCoordinate s hLF N (i + 1) z), by
        change (s.stage i).2.proj _ ∈ actualStableOpen s hLF N
        rw [actual_step_base, actualStableCoordinate_base]
        exact z.property⟩
    let b : actualStableStageOpen s hLF N i :=
      ⟨actualStableCoordinate s hLF N i z, by
        change (s.stage i).2.proj _ ∈ actualStableOpen s hLF N
        rw [actualStableCoordinate_base]
        exact z.property⟩
    have he : actualStableEquiv s hLF N i hNi a = actualStableEquiv s hLF N i hNi b := by
      apply Subtype.ext
      rw [actualStableEquiv_val, actualStableEquiv_val]
      change (actualTail s N i hNi).proj (actualStepMap s i
        (actualStableCoordinate s hLF N (i + 1) z)) =
        (actualTail s N i hNi).proj (actualStableCoordinate s hLF N i z)
      change ((actualTail s N i hNi).proj ∘ actualStepMap s i)
        (actualStableCoordinate s hLF N (i + 1) z) =
        (actualTail s N i hNi).proj (actualStableCoordinate s hLF N i z)
      rw [← BlowupTower.proj_step (hπ:=actualStepMap_isBlowup s i), ← actualTail_succ s hNi,
        actualStableCoordinate_down s hLF N (i + 1) (by omega),
        actualStableCoordinate_down s hLF N i hNi]
    exact congrArg Subtype.val ((actualStableEquiv s hLF N i hNi).injective he)

/-- The actual full thread extending a stabilized stage point. -/
def actualSigma (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ) :
    actualStableStageOpen s hLF N N → ActualCompatibleThread s :=
  fun z => ⟨fun i => actualStableCoordinate s hLF N i z,
    fun i => actualStableCoordinate_compatible s hLF N i z⟩

theorem actualSigma_stage_self (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N : ℕ) (z : actualStableStageOpen s hLF N N) :
    (actualSigma s hLF N z).val N = z.val := by
  simp [actualSigma, actualStableCoordinate]

theorem actualSigma_base (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N : ℕ) (z : actualStableStageOpen s hLF N N) :
    actualThreadBaseProjection s (actualSigma s hLF N z) = (s.stage N).2.proj z.val :=
  actualStableCoordinate_base s hLF N 0 z

theorem actualSigma_continuous (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N : ℕ) : Continuous (actualSigma s hLF N) :=
  (continuous_pi (fun i => (actualStableCoordinate_contMDiff s hLF N i).continuous)).subtype_mk _

theorem actualSigma_injective (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N : ℕ) : Injective (actualSigma s hLF N) := by
  intro a b hab
  apply Subtype.ext
  simpa only [actualSigma_stage_self] using congrArg (fun t : ActualCompatibleThread s => t.val N) hab

theorem actualSigma_recovers_thread (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N : ℕ) (t : ActualCompatibleThread s) (ht : actualThreadBaseProjection s t ∈ actualStableOpen s hLF N) :
    actualSigma s hLF N ⟨t.val N, by
      change (s.stage N).2.proj (t.val N) ∈ actualStableOpen s hLF N
      rwa [actualThread_base]⟩ = t := by
  apply Subtype.ext
  funext i
  change actualStableCoordinate s hLF N i _ = t.val i
  by_cases hi : i ≤ N
  · simp only [actualStableCoordinate, dif_pos hi]
    exact actualThread_down s t hi
  · let v : actualStableStageOpen s hLF N N :=
      ⟨t.val N, by
        change (s.stage N).2.proj (t.val N) ∈ actualStableOpen s hLF N
        rwa [actualThread_base]⟩
    let a : actualStableStageOpen s hLF N i :=
      ⟨actualStableCoordinate s hLF N i v, by
        change (s.stage i).2.proj (actualStableCoordinate s hLF N i v) ∈ actualStableOpen s hLF N
        rw [actualStableCoordinate_base, actualThread_base]
        exact ht⟩
    let b : actualStableStageOpen s hLF N i :=
      ⟨t.val i, by
        change (s.stage i).2.proj (t.val i) ∈ actualStableOpen s hLF N
        rwa [actualThread_base]⟩
    have he : actualStableEquiv s hLF N i (by omega) a =
        actualStableEquiv s hLF N i (by omega) b := by
      apply Subtype.ext
      rw [actualStableEquiv_val, actualStableEquiv_val]
      exact (actualStableCoordinate_down s hLF N i (by omega) v).trans
        (actualThread_down s t (by omega)).symm
    exact congrArg Subtype.val ((actualStableEquiv s hLF N i (by omega)).injective he)

theorem actualSigma_range (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ) :
    range (actualSigma s hLF N) =
      actualThreadBaseProjection s ⁻¹' (actualStableOpen s hLF N : Set X) := by
  ext t
  constructor
  · rintro ⟨z, rfl⟩
    change actualThreadBaseProjection s (actualSigma s hLF N z) ∈ actualStableOpen s hLF N
    rw [actualSigma_base]
    exact z.property
  · intro ht
    exact ⟨_, actualSigma_recovers_thread s hLF N t ht⟩

def actualThreadStableOpen (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ) :
    Opens (ActualCompatibleThread s) :=
  ⟨actualThreadBaseProjection s ⁻¹' (actualStableOpen s hLF N : Set X),
    (actualStableOpen s hLF N).isOpen.preimage (actualThreadBaseProjection_continuous s)⟩

private def actualSigmaInto (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ)
    (z : actualStableStageOpen s hLF N N) : actualThreadStableOpen s hLF N :=
  ⟨actualSigma s hLF N z, by
    change actualThreadBaseProjection s (actualSigma s hLF N z) ∈ actualStableOpen s hLF N
    exact (actualSigma_base s hLF N z).symm ▸ z.property⟩

private def actualSigmaOut (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ)
    (t : actualThreadStableOpen s hLF N) : actualStableStageOpen s hLF N N :=
  ⟨t.val.val N, by
    change (s.stage N).2.proj (t.val.val N) ∈ actualStableOpen s hLF N
    exact (actualThread_base s t.val N).symm ▸ t.property⟩

def actualSigmaHomeomorph (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ) :
    actualStableStageOpen s hLF N N ≃ₜ actualThreadStableOpen s hLF N where
  toFun := actualSigmaInto s hLF N
  invFun := actualSigmaOut s hLF N
  left_inv z := Subtype.ext (actualSigma_stage_self s hLF N z)
  right_inv t := Subtype.ext (actualSigma_recovers_thread s hLF N t.val t.property)
  continuous_toFun := (actualSigma_continuous s hLF N).subtype_mk _
  continuous_invFun := ((actualThreadStageProjection_continuous s N).comp
    continuous_subtype_val).subtype_mk _

theorem actualSigma_openEmbedding (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N : ℕ) : IsOpenEmbedding (actualSigma s hLF N) :=
  (actualThreadStableOpen s hLF N).isOpen.isOpenEmbedding_subtypeVal.comp
    (actualSigmaHomeomorph s hLF N).isOpenEmbedding

theorem actualSigma_cover (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    ∀ t : ActualCompatibleThread s, ∃ N z, actualSigma s hLF N z = t := by
  intro t
  obtain ⟨N, hN⟩ := actualStableOpen_cover s hLF (actualThreadBaseProjection s t)
  exact ⟨N, _, actualSigma_recovers_thread s hLF N t hN⟩

/-! ## Holomorphic overlap maps, constructed from the actual coordinates -/

private theorem actual_contMDiff_opens_mk {m : ℕ} {A : Type*} {B : Type*}
    [TopologicalSpace A] [ChartedSpace (ComplexModel m) A]
    [TopologicalSpace B] [ChartedSpace (ComplexModel n) B]
    (V : Opens B) (f : A → B)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hV : ∀ a, f a ∈ V) :
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (fun a => (⟨f a, hV a⟩ : V)) := by
  intro a
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.continuous.subtype_mk hV).continuousAt, ?_⟩
  exact ((contMDiffAt_iff_target.mp (hf a)).2 : _)

private abbrev actualOverlap (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N M : ℕ) :=
  actualEmbeddingOverlap (actualSigma s hLF N) (actualSigma s hLF M)
    (actualSigma_openEmbedding s hLF N) (actualSigma_openEmbedding s hLF M)

private theorem actualOverlap_base (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N M : ℕ) (a : actualOverlap s hLF N M) :
    actualThreadBaseProjection s (actualSigma s hLF N a.val) ∈ actualStableOpen s hLF M := by
  have ha := a.property
  change actualSigma s hLF N a.val ∈ range (actualSigma s hLF M) at ha
  rwa [actualSigma_range] at ha

private def actualChange (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N M : ℕ) (a : actualOverlap s hLF N M) : actualStableStageOpen s hLF M M :=
  ⟨(actualSigma s hLF N a.val).val M, by
    change (s.stage M).2.proj _ ∈ actualStableOpen s hLF M
    rw [actualThread_base]
    exact actualOverlap_base s hLF N M a⟩

private theorem actualChange_sigma (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N M : ℕ) (a : actualOverlap s hLF N M) :
    actualSigma s hLF M (actualChange s hLF N M a) = actualSigma s hLF N a.val :=
  actualSigma_recovers_thread s hLF M _ (actualOverlap_base s hLF N M a)

private theorem actualChange_contMDiff (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N M : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualChange s hLF N M) := by
  exact actual_contMDiff_opens_mk (actualStableStageOpen s hLF M M)
    (fun a : actualOverlap s hLF N M => actualStableCoordinate s hLF N M a.val)
    ((actualStableCoordinate_contMDiff s hLF N M).comp contMDiff_subtype_val) _

private def actualOverlapMap (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N M : ℕ) (a : actualOverlap s hLF N M) : actualOverlap s hLF M N :=
  ⟨actualChange s hLF N M a, ⟨a.val, (actualChange_sigma s hLF N M a).symm⟩⟩

private theorem actualOverlapMap_sigma (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N M : ℕ) (a : actualOverlap s hLF N M) :
    actualSigma s hLF M (actualOverlapMap s hLF N M a).val = actualSigma s hLF N a.val :=
  actualChange_sigma s hLF N M a

private theorem actualOverlapMap_contMDiff (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N M : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualOverlapMap s hLF N M) :=
  actual_contMDiff_opens_mk (actualOverlap s hLF M N) (actualChange s hLF N M)
    (actualChange_contMDiff s hLF N M) _

private def actualOverlapEquiv (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (N M : ℕ) : actualOverlap s hLF N M
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ actualOverlap s hLF M N where
  toFun := actualOverlapMap s hLF N M
  invFun := actualOverlapMap s hLF M N
  left_inv a := by
    apply Subtype.ext
    apply actualSigma_injective s hLF N
    exact (actualOverlapMap_sigma s hLF M N _).trans (actualOverlapMap_sigma s hLF N M a)
  right_inv a := by
    apply Subtype.ext
    apply actualSigma_injective s hLF M
    exact (actualOverlapMap_sigma s hLF N M _).trans (actualOverlapMap_sigma s hLF M N a)
  contMDiff_toFun := actualOverlapMap_contMDiff s hLF N M
  contMDiff_invFun := actualOverlapMap_contMDiff s hLF M N

/-- The charted structure is constructed after the actual product topology. -/
@[instance_reducible]
def actualLimitChartedSpace (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    ChartedSpace (ComplexModel n) (ActualCompatibleThread s) :=
  actualLiftedTerminalChartedSpace n (actualSigma s hLF)
    (actualSigma_openEmbedding s hLF) (actualSigma_cover s hLF)

private theorem actualLimit_isComplexManifold (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) :
    let := actualLimitChartedSpace s hLF
    IsComplexManifold n (ActualCompatibleThread s) := by
  let := actualLimitChartedSpace s hLF
  let : IsManifold 𝓘(ℂ,ComplexModel n) ∞ (ActualCompatibleThread s) :=
    actualLiftedTerminalChartedSpace_isManifold (actualSigma s hLF)
      (actualSigma_openEmbedding s hLF) (actualSigma_cover s hLF)
      (actualOverlapEquiv s hLF) (actualOverlapMap_sigma s hLF)
  have : SecondCountableTopology (ActualCompatibleThread s) :=
    secondCountable_of_actual_saturated_projection_atlas (actualThreadBaseProjection s)
      (actualStableOpen s hLF) (actualStableOpen_cover s hLF) (actualSigma s hLF)
      (actualSigma_openEmbedding s hLF) (actualSigma_range s hLF)
  dsimp only
  exact IsComplexManifold.mk

/-- The underlying topology remains exactly the actual thread subspace topology. -/
def actualLimitManifold (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) : CMfd.{u} n where
  carrier := ActualCompatibleThread s
  topologicalSpace := inferInstance
  chartedSpace := actualLimitChartedSpace s hLF
  isComplexManifold := actualLimit_isComplexManifold s hLF

def actualLimitStageProjection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (i : ℕ) : actualLimitManifold s hLF → (s.stage i).1 :=
  actualThreadStageProjection s i

def actualLimitBaseProjection (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    actualLimitManifold s hLF → X := actualThreadBaseProjection s

def actualLimitStableOpen (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ) :
    Opens (actualLimitManifold s hLF) := actualThreadStableOpen s hLF N

/-- The same sigma function with its constructed native bundle as explicit codomain. -/
def actualLimitSigma (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ) :
    actualStableStageOpen s hLF N N → actualLimitManifold s hLF := actualSigma s hLF N

theorem actualSigma_contMDiff (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (actualLimitSigma s hLF N) :=
  actualLiftedTerminal_local_inclusion_contMDiff (actualSigma s hLF)
    (actualSigma_openEmbedding s hLF) (actualSigma_cover s hLF)
    (actualOverlapEquiv s hLF) (actualOverlapMap_sigma s hLF) N

/-! The inverse is proved holomorphic from actual lifted chart formulas; it
is not inferred from a merely holomorphic homeomorphism. -/
private theorem actualSigma_inverse_contMDiff (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (N : ℕ) :
    let := actualLimitChartedSpace s hLF
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (actualSigmaHomeomorph s hLF N).symm := by
  dsimp only
  let := actualLimitChartedSpace s hLF
  let : IsComplexManifold n (ActualCompatibleThread s) := actualLimit_isComplexManifold s hLF
  intro z
  let x := (actualSigmaHomeomorph s hLF N).symm z
  let e := chartAt (ComplexModel n) x
  let L := e.lift_openEmbedding (actualSigma_openEmbedding s hLF N)
  have he : e ∈ maximalAtlas 𝓘(ℂ,ComplexModel n) ∞
      (actualStableStageOpen s hLF N N) := chart_mem_maximalAtlas x
  have hL : L ∈ maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (ActualCompatibleThread s) :=
    subset_maximalAtlas ⟨N, e, chart_mem_atlas (ComplexModel n) x, rfl⟩
  have hx : x ∈ e.source := mem_chart_source (ComplexModel n) x
  have hz : z.val = actualSigma s hLF N x :=
    (congrArg Subtype.val ((actualSigmaHomeomorph s hLF N).apply_symm_apply z)).symm
  have hzL : z.val ∈ L.source := by rw [hz]; exact ⟨x, hx, rfl⟩
  have hLz : L z.val = e x := by
    rw [hz]
    exact OpenPartialHomeomorph.lift_openEmbedding_apply e (actualSigma_openEmbedding s hLF N)
  have hholL : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun w : actualThreadStableOpen s hLF N => L w.val) z :=
    (contMDiffAt_of_mem_maximalAtlas hL hzL).comp z contMDiff_subtype_val.contMDiffAt
  have hhole : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm (L z.val) := by
    rw [hLz]
    exact contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)
  have hh : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun w : actualThreadStableOpen s hLF N => e.symm (L w.val)) z := hhole.comp z hholL
  apply hh.congr_of_eventuallyEq
  filter_upwards [(L.open_source.preimage continuous_subtype_val).mem_nhds hzL] with w hw
  obtain ⟨y, hy, hyw⟩ := hw
  have hxy : (actualSigmaHomeomorph s hLF N).symm w = y := by
    apply actualSigma_injective s hLF N
    exact (congrArg Subtype.val ((actualSigmaHomeomorph s hLF N).apply_symm_apply w)).trans hyw.symm
  change (actualSigmaHomeomorph s hLF N).symm w = e.symm (L w.val)
  rw [hxy, ← hyw, OpenPartialHomeomorph.lift_openEmbedding_apply, e.left_inv hy]

/-- The actual stabilized chart, with BOTH holomorphic directions produced internally. -/
def actualSigmaBiholomorph (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (N : ℕ) :
    actualStableStageOpen s hLF N N
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ actualLimitStableOpen s hLF N where
  toEquiv := (actualSigmaHomeomorph s hLF N).toEquiv
  contMDiff_toFun := actual_contMDiff_opens_mk (actualLimitStableOpen s hLF N)
    (actualLimitSigma s hLF N) (actualSigma_contMDiff s hLF N) _
  contMDiff_invFun := actualSigma_inverse_contMDiff s hLF N

theorem actualLimitStageProjection_contMDiff (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (i : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualLimitStageProjection s hLF i) := by
  intro t
  obtain ⟨N, hN⟩ := actualStableOpen_cover s hLF (actualThreadBaseProjection s t)
  let z : actualLimitStableOpen s hLF N := ⟨t, hN⟩
  apply (contMDiffAt_subtype_iff (x := z)).mp
  have hh := ((actualStableCoordinate_contMDiff s hLF N i).comp
    (actualSigmaBiholomorph s hLF N).symm.contMDiff).contMDiffAt (x := z)
  apply hh.congr_of_eventuallyEq
  exact Eventually.of_forall fun w => by
    have he := congrArg (fun a : ActualCompatibleThread s => a.val i)
      (congrArg Subtype.val ((actualSigmaHomeomorph s hLF N).apply_symm_apply w))
    exact he.symm

theorem actualLimitBaseProjection_contMDiff (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualLimitBaseProjection s hLF) :=
  (s.stage 0).2.contMDiff_proj.comp (actualLimitStageProjection_contMDiff s hLF 0)

theorem actualLimitStageProjection_compatible (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (i : ℕ) (t : actualLimitManifold s hLF) :
    actualStepMap s i (actualLimitStageProjection s hLF (i + 1) t) =
      actualLimitStageProjection s hLF i t := t.property i

theorem actualLimitStageProjection_tail (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) {j i : ℕ} (h : j ≤ i)
    (t : actualLimitManifold s hLF) :
    (actualTail s j i h).proj (actualLimitStageProjection s hLF i t) =
      actualLimitStageProjection s hLF j t := actualThread_down s t h

theorem actualLimitStageProjection_base (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (i : ℕ) (t : actualLimitManifold s hLF) :
    (s.stage i).2.proj (actualLimitStageProjection s hLF i t) =
      actualLimitBaseProjection s hLF t := actualThread_base s t i

private theorem actualSigma_stage_of_le (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) {i N : ℕ} (hi : i ≤ N)
    (z : actualStableStageOpen s hLF N N) :
    actualLimitStageProjection s hLF i (actualSigma s hLF N z) =
      (actualTail s i N hi).proj z.val := by
  simp only [actualLimitStageProjection, actualThreadStageProjection, actualSigma,
    actualStableCoordinate, dif_pos hi]

/-! ## Properness of EVERY actual stage projection -/

theorem actualLimitStageProjection_isProperMap (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) (i : ℕ) :
    IsProperMap (actualLimitStageProjection s hLF i) := by
  let : LocallyCompactSpace (s.stage i).1 :=
    ChartedSpace.locallyCompactSpace (ComplexModel n) (s.stage i).1
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨(actualLimitStageProjection_contMDiff s hLF i).continuous, ?_⟩
  intro K hK
  have hbaseK : IsCompact ((s.stage i).2.proj '' K) :=
    hK.image (s.stage i).2.contMDiff_proj.continuous
  obtain ⟨N₀, hN₀⟩ := exists_compact_subset_actualStableOpen s hLF hbaseK
  let N := max i N₀
  have hiN : i ≤ N := le_max_left _ _
  have hN : (s.stage i).2.proj '' K ⊆ actualStableOpen s hLF N :=
    fun x hx => actualStableOpen_mono s hLF (le_max_right _ _) (hN₀ hx)
  let T := actualTail s i N hiN
  let A : Set (s.stage N).1 := T.proj ⁻¹' K
  have hA : IsCompact A := (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK
  have hAV : A ⊆ range (Subtype.val : actualStableStageOpen s hLF N N → (s.stage N).1) := by
    intro z hz
    have hzN : z ∈ actualStableStageOpen s hLF N N := by
      change (s.stage N).2.proj z ∈ actualStableOpen s hLF N
      rw [← actualTail_base s hiN z]
      exact hN ⟨T.proj z, hz, rfl⟩
    exact ⟨⟨z, hzN⟩, rfl⟩
  let S : Set (actualStableStageOpen s hLF N N) := Subtype.val ⁻¹' A
  have hS : IsCompact S := (Topology.IsEmbedding.subtypeVal).isInducing.isCompact_preimage' hA hAV
  have heq : actualLimitStageProjection s hLF i ⁻¹' K = actualSigma s hLF N '' S := by
    ext t
    constructor
    · intro ht
      have htN : actualThreadBaseProjection s t ∈ actualStableOpen s hLF N := by
        rw [← actualThread_base s t i]
        exact hN ⟨t.val i, ht, rfl⟩
      let z : actualStableStageOpen s hLF N N :=
        ⟨t.val N, by
          change (s.stage N).2.proj ((show ActualCompatibleThread s from t).val N) ∈ actualStableOpen s hLF N
          rw [actualThread_base]
          exact htN⟩
      have hz : z ∈ S := by
        have hd := actualThread_down s (show ActualCompatibleThread s from t) hiN
        change (actualTail s i N hiN).proj ((show ActualCompatibleThread s from t).val N) ∈ K
        rw [hd]
        exact ht
      exact ⟨z, hz, actualSigma_recovers_thread s hLF N t htN⟩
    · rintro ⟨z, hz, rfl⟩
      change actualLimitStageProjection s hLF i (actualSigma s hLF N z) ∈ K
      rw [actualSigma_stage_of_le s hLF hiN]
      exact hz
  rw [heq]
  exact hS.image (actualSigma_continuous s hLF N)

theorem actualLimitBaseProjection_isProperMap (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) : IsProperMap (actualLimitBaseProjection s hLF) :=
  (HironakaLocalPrincipalization.isProperMap_proj (s.stage 0).2).comp
    (actualLimitStageProjection_isProperMap s hLF 0)

/-! ## The universal continuous and holomorphic compatible cones -/

/-- The actual coordinate tuple is the universal cone map.  Compatibility,
not a terminality or limit-geometry certificate, is the natural cone input. -/
def actualConeLift (s : GrowingSeq X) {Z : Type v}
    (f : ∀ i, Z → (s.stage i).1)
    (hcomp : ∀ i z, actualStepMap s i (f (i + 1) z) = f i z) :
    Z → ActualCompatibleThread s := fun z => ⟨fun i => f i z, fun i => hcomp i z⟩

theorem actualConeLift_stage (s : GrowingSeq X) {Z : Type v}
    (f : ∀ i, Z → (s.stage i).1)
    (hcomp : ∀ i z, actualStepMap s i (f (i + 1) z) = f i z) (i : ℕ) (z : Z) :
    actualThreadStageProjection s i (actualConeLift s f hcomp z) = f i z := rfl

theorem actualConeLift_unique (s : GrowingSeq X) {Z : Type v}
    (f : ∀ i, Z → (s.stage i).1)
    (hcomp : ∀ i z, actualStepMap s i (f (i + 1) z) = f i z)
    (g : Z → ActualCompatibleThread s) (hg : ∀ i z, actualThreadStageProjection s i (g z) = f i z) :
    g = actualConeLift s f hcomp := by
  funext z
  apply Subtype.ext
  funext i
  exact hg i z

theorem actualConeLift_continuous (s : GrowingSeq X) {Z : Type v} [TopologicalSpace Z]
    (f : ∀ i, Z → (s.stage i).1)
    (hcomp : ∀ i z, actualStepMap s i (f (i + 1) z) = f i z)
    (hf : ∀ i, Continuous (f i)) : Continuous (actualConeLift s f hcomp) :=
  (continuous_pi hf).subtype_mk _

/-- The same coordinate tuple with the constructed native limit bundle as codomain. -/
def actualLimitConeLift (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) {Z : Type v}
    (f : ∀ i, Z → (s.stage i).1)
    (hcomp : ∀ i z, actualStepMap s i (f (i + 1) z) = f i z) :
    Z → actualLimitManifold s hLF := actualConeLift s f hcomp

theorem actualLimit_universal_continuous (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) {Z : Type v} [TopologicalSpace Z]
    (f : ∀ i, Z → (s.stage i).1)
    (hcomp : ∀ i z, actualStepMap s i (f (i + 1) z) = f i z)
    (hf : ∀ i, Continuous (f i)) :
    ∃! g : Z → actualLimitManifold s hLF,
      Continuous g ∧ ∀ i z, actualLimitStageProjection s hLF i (g z) = f i z := by
  refine ⟨actualLimitConeLift s hLF f hcomp, ⟨actualConeLift_continuous s f hcomp hf, fun _ _ => rfl⟩, ?_⟩
  intro g hg
  exact actualConeLift_unique s f hcomp g hg.2

theorem actualConeLift_contMDiff (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    {m : ℕ} {Z : CMfd.{v} m} (f : ∀ i, Z → (s.stage i).1)
    (hcomp : ∀ i z, actualStepMap s i (f (i + 1) z) = f i z)
    (hf : ∀ i, ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (f i)) :
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞
      (actualLimitConeLift s hLF f hcomp) := by
  intro z
  let F := actualConeLift s f hcomp
  obtain ⟨N, hN⟩ := actualStableOpen_cover s hLF (actualThreadBaseProjection s (F z))
  let V : Opens Z :=
    ⟨(actualThreadBaseProjection s ∘ F) ⁻¹' (actualStableOpen s hLF N : Set X),
      (actualStableOpen s hLF N).isOpen.preimage
        ((actualThreadBaseProjection_continuous s).comp
          (actualConeLift_continuous s f hcomp (fun i => (hf i).continuous)))⟩
  let g : V → actualStableStageOpen s hLF N N := fun w =>
    ⟨f N w.val, by
      change (s.stage N).2.proj ((F w.val).val N) ∈ actualStableOpen s hLF N
      rw [actualThread_base]
      exact w.property⟩
  have hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g :=
    actual_contMDiff_opens_mk (actualStableStageOpen s hLF N N) (fun w : V => f N w.val)
      ((hf N).comp contMDiff_subtype_val) _
  let w : V := ⟨z, hN⟩
  apply (contMDiffAt_subtype_iff (x := w)).mp
  have hh := ((actualSigma_contMDiff s hLF N).comp hg).contMDiffAt (x := w)
  apply hh.congr_of_eventuallyEq
  exact Eventually.of_forall fun a => (actualSigma_recovers_thread s hLF N (F a.val) a.property).symm

theorem actualLimit_universal_holomorphic (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) {m : ℕ} {Z : CMfd.{v} m}
    (f : ∀ i, Z → (s.stage i).1)
    (hcomp : ∀ i z, actualStepMap s i (f (i + 1) z) = f i z)
    (hf : ∀ i, ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (f i)) :
    ∃! g : Z → actualLimitManifold s hLF,
      ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      ∀ i z, actualLimitStageProjection s hLF i (g z) = f i z := by
  refine ⟨actualLimitConeLift s hLF f hcomp, ⟨actualConeLift_contMDiff s hLF f hcomp hf, fun _ _ => rfl⟩, ?_⟩
  intro g hg
  exact actualConeLift_unique s f hcomp g hg.2

/-- The pure geometric GIVEN-LF endpoint.  All named objects in this statement
are constructed above from the original actual history and footprint LF.
The continuous and holomorphic universal cone properties are the preceding
two theorems, valid for arbitrary source dimension and universe. -/
theorem actual_given_locallyFinite_blowup_limit_geometry (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) :
    (∀ i, ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (actualLimitStageProjection s hLF i) ∧ IsProperMap (actualLimitStageProjection s hLF i)) ∧
    (ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualLimitBaseProjection s hLF) ∧
      IsProperMap (actualLimitBaseProjection s hLF)) ∧
    (∀ N, IsOpenEmbedding (actualSigma s hLF N) ∧
      range (actualSigma s hLF N) =
        actualLimitBaseProjection s hLF ⁻¹' (actualStableOpen s hLF N : Set X)) ∧
    (∀ t : actualLimitManifold s hLF, ∃ N z, actualSigma s hLF N z = t) := by
  exact ⟨fun i => ⟨actualLimitStageProjection_contMDiff s hLF i,
      actualLimitStageProjection_isProperMap s hLF i⟩,
    ⟨actualLimitBaseProjection_contMDiff s hLF, actualLimitBaseProjection_isProperMap s hLF⟩,
    (fun N => ⟨actualSigma_openEmbedding s hLF N, actualSigma_range s hLF N⟩),
    actualSigma_cover s hLF⟩

end

end TranscendentalNakamaye.Pending.HironakaActualLocallyFiniteBlowupLimitGeometry
