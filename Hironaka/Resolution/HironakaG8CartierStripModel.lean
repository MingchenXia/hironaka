import Hironaka.Resolution.HironakaG8PhysicalIncomingRankObstruction
import Hironaka.Analytic.HolomorphicGermReducednessBridge
import Hironaka.Resolution.HironakaG3EmptyAwareComposition

/-! # A literal Cartier-chart model with unbounded incoming occupied stages -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CartierStripModel
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupRestrictOpen BlowupTowerIsoTail
  ResolutionInvariantSpec RestrictEmptyTower CodimOneSupport HolomorphicGermReducednessBridge
  HironakaG3EmptyAwareHistory HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaG8RankedEmptyPadding MaxLocusLocal
  HironakaG8PhysicalIncomingRankObstruction

open ResolutionInvariantExt (IsEmptyTower)

abbrev X := CMfd.of (n := 2) (ComplexModel 2)

def verticalValue (i : ℤ) (k : ℕ) : ℂ := (i : ℂ) + (k : ℂ) * Complex.I

theorem verticalValue_injective (i : ℤ) : Function.Injective (verticalValue i) := by
  intro k l h
  have h' := congrArg Complex.im h
  simpa [verticalValue,Complex.mul_im] using h'

def hyperplane (j : Fin 2) (c : ℂ) : Set X := {z | z j = c}

def pointOn (j : Fin 2) (c : ℂ) : X := PiLp.single 2 j c

theorem pointOn_mem (j : Fin 2) (c : ℂ) : pointOn j c ∈ hyperplane j c := by
  simp [pointOn,hyperplane]

private theorem hyperplane_regular (j : Fin 2) (c : ℂ) (z : X) (hz : z ∈ hyperplane j c) :
    RegularAtDim (n := 2) (hyperplane j c) z 1 := by
  have hc : (complexChartAt (n := 2) z).val = OpenPartialHomeomorph.refl (ComplexModel 2) := by
    simp [complexChartAt]
  change z j = c at hz
  apply regularAtDim_of_eventuallyEq_unit_mul_coordinate
    (N := univ) (f := fun w : X => w j - c) (u := fun _ => 1) (j := j)
    isOpen_univ (mem_univ _) (by rw [hc]; exact subset_rfl)
    (((EuclideanSpace.proj (𝕜 := ℂ) j).differentiable.sub_const c).differentiableOn)
  · intro y _ _
    rw [hc]
    exact sub_eq_zero.symm
  · exact hz
  · exact differentiableAt_const _
  · simp
  · rw [hc]
    exact Eventually.of_forall fun y => by simp [hz]

private theorem hyperplane_closed (j : Fin 2) (c : ℂ) : IsClosed (hyperplane j c) :=
  isClosed_singleton.preimage (EuclideanSpace.proj (𝕜 := ℂ) j).continuous

private theorem hyperplane_thin (j : Fin 2) (c : ℂ) : interior (hyperplane j c) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hN : ∀ᶠ y in 𝓝 x, y ∈ hyperplane j c := mem_interior_iff_mem_nhds.mp hx
  have hu : ∀ᶠ y in 𝓝 x, y ∈ (univ : Set X) ↔ y ∈ hyperplane j c :=
    hN.mono fun _ hy => iff_of_true trivial hy
  have h2 := regularAtDim_of_eventually_mem_iff (n := 2) hu (AnalyticIrreducibleComponents.regularAtDim_univ x)
  have h1 := hyperplane_regular j c x (interior_subset hx)
  have he := RegularPointDimension.eq_of_regularAtDim h1 h2
  omega

theorem hyperplane_identity_blowup (j : Fin 2) (c : ℂ) : IsBlowupAlong 2 (hyperplane j c) (id : X → X) :=
  BlowupExistenceCodimOne.isBlowupAlong_id_of_codimOne
    ⟨hyperplane_closed j c,fun z hz => ⟨1,hyperplane_regular j c z hz⟩⟩
    (hyperplane_thin j c) (fun z hz => ⟨1,hyperplane_regular j c z hz,rfl⟩)

/-- Open horizontal-coordinate strips of a locally shifted affine atlas. -/
def strip (i : ℤ) : Opens X :=
  ⟨(fun z : X => (z 0).re) ⁻¹' Ioo ((i : ℝ) - 3/4) ((i : ℝ) + 3/4),
    isOpen_Ioo.preimage (Complex.continuous_re.comp (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).continuous)⟩

def verticalHead (i : ℤ) : ℕ → BlowupTower X X
  | 0 => .refl
  | k+1 => .step (verticalHead i k) (hyperplane 0 (verticalValue i k)) id
    (hyperplane_identity_blowup 0 (verticalValue i k))

def chartTower (i : ℤ) : BlowupTower X X :=
  .step (verticalHead i i.natAbs) (hyperplane 1 0) id (hyperplane_identity_blowup 1 0)

theorem prefix_length (i : ℤ) (k : ℕ) : (verticalHead i k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [verticalHead,BlowupTower.length_step,ih]

theorem prefix_proj (i : ℤ) (k : ℕ) : (verticalHead i k).proj = id := by
  induction k with
  | zero => rfl
  | succ k ih => rw [verticalHead,BlowupTower.proj_step,ih,Function.comp_id]

theorem chart_proj (i : ℤ) : (chartTower i).proj = id := by
  rw [chartTower,BlowupTower.proj_step,prefix_proj,Function.comp_id]

theorem vertical_subset_strip (i : ℤ) (k : ℕ) : hyperplane 0 (verticalValue i k) ⊆ strip i := by
  intro z hz
  change z 0 = _ at hz
  change ((i : ℝ)-3/4 < (z 0).re ∧ (z 0).re < (i : ℝ)+3/4)
  rw [hz]
  simp [verticalValue,Complex.mul_re]

theorem vertical_misses_other_strip (i j : ℤ) (hij : i ≠ j) (k : ℕ) :
    Disjoint (strip j : Set X) (hyperplane 0 (verticalValue i k)) := by
  rw [Set.disjoint_left]
  intro z hz hc
  change z 0 = _ at hc
  change ((j : ℝ)-3/4 < (z 0).re ∧ (z 0).re < (j : ℝ)+3/4) at hz
  rw [hc] at hz
  simp [verticalValue,Complex.mul_re] at hz
  rcases lt_or_gt_of_ne hij with hl | hr
  · have h : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    linarith [hz.1]
  · have h : (j : ℝ)+1 ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    linarith [hz.2]

/-- The physical chart is the literal open restriction of its finite tower. -/
abbrev chart (i : ℤ) := restrict (strip i) (chartTower i)

theorem strips_cover (z : X) : ∃ i : ℤ, z ∈ strip i := by
  let x := (z 0).re
  let i := ⌊x + 1/2⌋
  refine ⟨i,?_⟩
  change (i : ℝ)-3/4 < x ∧ x < (i : ℝ)+3/4
  have h₁ := Int.floor_le (x+1/2)
  have h₂ := Int.lt_floor_add_one (x+1/2)
  exact ⟨by change (i:ℝ) ≤ x+1/2 at h₁; linarith,
    by change x+1/2 < (i:ℝ)+1 at h₂; linarith⟩

theorem strips_locally_finite : LocallyFinite (fun i : ℤ => (strip i : Set X)) := by
  intro z
  obtain ⟨i,hi⟩ := strips_cover z
  refine ⟨strip i,(strip i).isOpen.mem_nhds hi,?_⟩
  apply (Set.finite_Icc (i-1) (i+1)).subset
  rintro j ⟨y,hyj,hyi⟩
  change ((j : ℝ)-3/4 < (y 0).re ∧ (y 0).re < (j : ℝ)+3/4) at hyj
  change ((i : ℝ)-3/4 < (y 0).re ∧ (y 0).re < (i : ℝ)+3/4) at hyi
  constructor
  · by_contra h
    have h' : (j : ℝ)+2 ≤ (i : ℝ) := by exact_mod_cast (show j+2 ≤ i by omega)
    linarith [hyj.2,hyi.1]
  · by_contra h
    have h' : (i : ℝ)+2 ≤ (j : ℝ) := by exact_mod_cast (show i+2 ≤ j by omega)
    linarith [hyj.1,hyi.2]

/-- The genuine restricted prefix sees exactly its original number
of occupied vertical divisors. -/
theorem strip_incoming_count (i : ℤ) (k : ℕ) :
    countCentresMeeting univ (restrict (strip i) (verticalHead i k)) = k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    let T := verticalHead i k
    let x := pointOn 0 (verticalValue i k)
    have hx : x ∈ hyperplane 0 (verticalValue i k) := pointOn_mem _ _
    have hU : x ∈ openPreimage T (strip i) := by
      change T.proj x ∈ strip i
      rw [show T.proj = id from prefix_proj i k]
      exact vertical_subset_strip i k hx
    change countCentresMeeting univ (restrict (strip i) T) +
      (if (((Subtype.val : openPreimage T (strip i) → X) ⁻¹' hyperplane 0 (verticalValue i k)) ∩
        (restrict (strip i) T).proj ⁻¹' univ).Nonempty then 1 else 0) = k+1
    have hNot : (((Subtype.val : openPreimage T (strip i) → X) ⁻¹' hyperplane 0 (verticalValue i k)) ∩
        (restrict (strip i) T).proj ⁻¹' univ).Nonempty := ⟨⟨x,hU⟩,hx,trivial⟩
    rw [if_pos hNot,ih]

private theorem prefix_over_own_strip (i : ℤ) : ∀ k, CentresOver (strip i) (verticalHead i k)
  | 0 => trivial
  | k+1 => ⟨prefix_over_own_strip i k,fun z hz => by
      rw [prefix_proj]
      exact vertical_subset_strip i k hz⟩

private theorem prefix_empty_on_overlap {i j : ℤ} (h : i ≠ j) (k : ℕ) :
    IsEmptyTower (restrict (strip i ⊓ strip j) (verticalHead i k)) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨ih,?_⟩
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hZ : (verticalHead i k).proj z.val ∈ strip i ⊓ strip j := z.property
    rw [prefix_proj] at hZ
    exact Set.disjoint_left.mp (vertical_misses_other_strip i j h k) hZ.2 hz

private theorem empty_cmp_same_base {n : ℕ} {A B C : CMfd.{0} n}
    (T : BlowupTower A B) (S : BlowupTower A C) (hT : IsEmptyTower T) (hS : IsEmptyTower S) :
    ∃ e : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ C,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) T S e := by
  revert hS
  induction S with
  | refl =>
    intro _
    induction T with
    | refl => exact ⟨_,.refl⟩
    | @step B C T D π hπ ih =>
      obtain ⟨hh,rfl⟩ := hT
      obtain ⟨e,he⟩ := ih hh
      obtain ⟨β,_,hCmp⟩ := exists_emptyAware_left he hπ
      exact ⟨_,hCmp⟩
  | @step B C S D π hπ ih =>
    rintro ⟨hh,rfl⟩
    obtain ⟨e,he⟩ := ih hh
    obtain ⟨β,_,hCmp⟩ := exists_emptyAware_right he hπ
    exact ⟨_,hCmp⟩

private def endpointEquiv (i : ℤ) (U : Opens X) :
    CMfd.of (n := 2) (openPreimage (chartTower i) U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel 2),𝓘(ℂ,ComplexModel 2)⟯ CMfd.of (n := 2) U :=
  opensCongr (by ext x; change (chartTower i).proj x ∈ U ↔ x ∈ U; rw [chart_proj]; rfl)

private theorem overlap_before_val {i j : ℤ} (U : Opens X)
    (e : CMfd.of (n := 2) (openPreimage (verticalHead i i.natAbs) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel 2),𝓘(ℂ,ComplexModel 2)⟯
          CMfd.of (n := 2) (openPreimage (verticalHead j j.natAbs) U))
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel 2) (CMfd.of (n := 2) U) ∞)
      (restrict U (verticalHead i i.natAbs)) (restrict U (verticalHead j j.natAbs)) e) :
    ∀ z, (e z).val = z.val := by
  intro z
  have hEq := congrArg Subtype.val (emptyAware_proj_comm h z)
  rw [proj_restrict] at hEq
  change (verticalHead j j.natAbs).proj (e z).val = ((restrict U (verticalHead i i.natAbs)).proj z).val at hEq
  rw [proj_restrict,prefix_proj,prefix_proj] at hEq
  exact hEq

/-- Actual physical towers compare over every literal overlap. The
overlap of distinct strips erases all vertical predecessors of either chart and matches its
true horizontal terminal blowup with the same ambient endpoint map. -/
theorem strip_physical_overlap (i j : ℤ) :
    let U := strip i ⊓ strip j
    ∃ e : CMfd.of (n := 2) (openPreimage (chartTower i) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel 2),𝓘(ℂ,ComplexModel 2)⟯
          CMfd.of (n := 2) (openPreimage (chartTower j) U),
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel 2) (CMfd.of (n := 2) U) ∞)
        (restrict U (chartTower i)) (restrict U (chartTower j)) e ∧
      ∀ z, (e z).val = z.val := by
  intro U
  by_cases h : i = j
  · subst j
    exact ⟨_,emptyAware_of_isTowerIso (IsTowerIso.refl_self _),fun _ => rfl⟩
  · have hI : IsEmptyTower (restrict U (verticalHead i i.natAbs)) := prefix_empty_on_overlap h _
    have hu : U = strip j ⊓ strip i := inf_comm _ _
    have hJ : IsEmptyTower (restrict U (verticalHead j j.natAbs)) := by
      rw [hu]
      exact prefix_empty_on_overlap (Ne.symm h) _
    obtain ⟨p,hp⟩ := empty_cmp_same_base _ _ hI hJ
    let e := (endpointEquiv i U).trans (endpointEquiv j U).symm
    have he : ∀ z, (e z).val = z.val := fun _ => rfl
    have hv := overlap_before_val U p hp
    refine ⟨e,?_ ,he⟩
    refine EmptyAwareTowerIso.step hp _ _ e ?_ ?_
    · intro z
      apply Subtype.ext
      exact (he z).trans (hv _).symm
    · ext z
      change (p z).val ∈ hyperplane 1 0 ↔ z.val ∈ hyperplane 1 0
      rw [hv]

abbrev chartBase (i : ℤ) := CMfd.of (n := 2) (strip i)
abbrev chartBefore (i : ℤ) := CMfd.of (n := 2) (openPreimage (verticalHead i i.natAbs) (strip i))
abbrev chartTarget (i : ℤ) := CMfd.of (n := 2) (openPreimage (chartTower i) (strip i))
abbrev chartHead (i : ℤ) : BlowupTower (chartBase i) (chartBefore i) :=
  restrict (strip i) (verticalHead i i.natAbs)

def chartCentre (i : ℤ) : Set (chartBefore i) :=
  (Subtype.val : openPreimage (verticalHead i i.natAbs) (strip i) → X) ⁻¹' hyperplane 1 0

def chartLast (i : ℤ) (x : chartTarget i) : chartBefore i := ⟨x.val,x.property⟩

theorem chartLast_blowup (i : ℤ) : IsBlowupAlong 2 (chartCentre i) (chartLast i) :=
  isBlowupAlong_restrict (hyperplane_identity_blowup 1 0) (openPreimage (verticalHead i i.natAbs) (strip i))
    ((openPreimage (verticalHead i i.natAbs) (strip i)).isOpen.preimage
      (hyperplane_identity_blowup 1 0).contMDiff.continuous)

/-- The penultimate and final data are the literal steps of the chart. -/
theorem chart_eq_step (i : ℤ) :
    chart i = .step (chartHead i) (chartCentre i) (chartLast i) (chartLast_blowup i) := rfl

/-- The double open restrictions are literally the common ambient
overlap, with the standard inclusions on points. -/
theorem literal_chart_overlap_nested_isos (i j : ℤ) :
    let U := strip i ⊓ strip j
    (∃ e, IsTowerIso (nestedOpensDiffeo (n := 2) (inf_le_left : U ≤ strip i))
      (restrict (nestedOpens (strip i) U) (chart i)) (restrict U (chartTower i)) e) ∧
    (∃ e, IsTowerIso (nestedOpensDiffeo (n := 2) (inf_le_right : U ≤ strip j))
      (restrict (nestedOpens (strip j) U) (chart j)) (restrict U (chartTower j)) e) := by
  intro U
  exact ⟨⟨_,isTowerIso_restrict_nestedOpens (inf_le_left : U ≤ strip i) _⟩,
    ⟨_,isTowerIso_restrict_nestedOpens (inf_le_right : U ≤ strip j) _⟩⟩

/-- The literal nested restrictions of any two open charts have genuine
empty-aware physical comparisons on their shared base. -/
theorem strip_nested_physical_overlap (i j : ℤ) :
    let U := strip i ⊓ strip j
    ∃ φ : CMfd.of (n := 2) (nestedOpens (strip i) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel 2),𝓘(ℂ,ComplexModel 2)⟯ CMfd.of (n := 2) (nestedOpens (strip j) U),
      ∃ χ : CMfd.of (n := 2) (openPreimage (chart i) (nestedOpens (strip i) U))
          ≃ₘ⟮𝓘(ℂ,ComplexModel 2),𝓘(ℂ,ComplexModel 2)⟯
            CMfd.of (n := 2) (openPreimage (chart j) (nestedOpens (strip j) U)),
        EmptyAwareTowerIso φ (restrict (nestedOpens (strip i) U) (chart i))
          (restrict (nestedOpens (strip j) U) (chart j)) χ := by
  intro U
  obtain ⟨⟨l,hl⟩,⟨r,hr⟩⟩ := literal_chart_overlap_nested_isos i j
  obtain ⟨e,he,_⟩ := strip_physical_overlap i j
  exact ⟨_,_,HironakaG3EmptyAwareComposition.trans (emptyAware_of_isTowerIso hl)
    (HironakaG3EmptyAwareComposition.trans he (emptyAware_of_isTowerIso hr.symm))⟩

/-- Incoming and terminal loci meet on their actual base chart. Thus
the displayed predecessors are not disjoint from the terminal locus. -/
theorem vertical_meets_horizontal_in_own_chart (i : ℤ) (k : ℕ) :
    ((strip i : Set X) ∩ hyperplane 0 (verticalValue i k) ∩ hyperplane 1 0).Nonempty := by
  let z := pointOn 0 (verticalValue i k)
  have hz : z ∈ hyperplane 0 (verticalValue i k) := pointOn_mem _ _
  refine ⟨z,⟨vertical_subset_strip i k hz,hz⟩,?_⟩
  simp [z,pointOn,hyperplane,show (1 : Fin 2) ≠ 0 by decide]

theorem incoming_hyperplanes_distinct (i : ℤ) :
    Function.Injective (fun k => hyperplane 0 (verticalValue i k)) := by
  intro k l h
  apply verticalValue_injective i
  have hz := pointOn_mem (j := (0 : Fin 2)) (verticalValue i k)
  change hyperplane 0 (verticalValue i k) = hyperplane 0 (verticalValue i l) at h
  have he : pointOn 0 (verticalValue i k) ∈ hyperplane 0 (verticalValue i l) := by
    rw [← h]
    exact hz
  simpa [pointOn,hyperplane] using he

theorem adjacent_horizontal_overlap (i : ℤ) :
    ∃ x : X, x ∈ (strip i ⊓ strip (i+1) : Opens X) ∧ x ∈ hyperplane 1 0 := by
  let x := pointOn 0 ((i : ℂ) + (1/2 : ℂ))
  have hx : (x 0).re = (i : ℝ)+1/2 := by
    simp [x,pointOn]
  have hxZ : x ∈ hyperplane 1 0 := by
    simp [x,pointOn,hyperplane,show (1 : Fin 2) ≠ 0 by decide]
  refine ⟨x,⟨?_,?_⟩,hxZ⟩
  · change (i : ℝ)-3/4 < (x 0).re ∧ (x 0).re < (i : ℝ)+3/4
    rw [hx]
    constructor <;> linarith
  · change ((i+1 : ℤ) : ℝ)-3/4 < (x 0).re ∧ (x 0).re < ((i+1 : ℤ) : ℝ)+3/4
    rw [hx]
    push_cast
    constructor <;> linarith

def leftLink (a : ℕ) : Opens (chartBase (a : ℤ)) :=
  nestedOpens (strip (a : ℤ)) (strip (a : ℤ) ⊓ strip ((a+1 : ℕ) : ℤ))

def rightLink (a : ℕ) : Opens (chartBase ((a+1 : ℕ) : ℤ)) :=
  nestedOpens (strip ((a+1 : ℕ) : ℤ)) (strip (a : ℤ) ⊓ strip ((a+1 : ℕ) : ℤ))

private theorem horizontal_trace_nonempty (i : ℤ) (U : Opens X)
    (h : U ≤ strip i) (hx : ((U : Set X) ∩ hyperplane 1 0).Nonempty) :
    ((Subtype.val : openPreimage (chartHead i) (nestedOpens (strip i) U) → chartBefore i)
      ⁻¹' chartCentre i).Nonempty := by
  obtain ⟨x,hxU,hxH⟩ := hx
  have hxP : x ∈ openPreimage (verticalHead i i.natAbs) (strip i) := by
    change (verticalHead i i.natAbs).proj x ∈ strip i
    rw [prefix_proj]
    exact h hxU
  let y : chartBefore i := ⟨x,hxP⟩
  have hyU : y ∈ openPreimage (chartHead i) (nestedOpens (strip i) U) := by
    change (((chartHead i).proj y : strip i) : X) ∈ U
    rw [proj_restrict,prefix_proj]
    exact hxU
  exact ⟨⟨y,hyU⟩,hxH⟩

/-- All raw physical charts are finite and locally compatible, but their
matched occupied terminal blowups admit no common natural clock that
retains each chart's actual ordered occupied stages. -/
theorem cartier_strip_family_has_no_synchronized_natural_clock :
    ¬ ∃ (i r : ℕ → ℕ)
      (D : ∀ a : ℕ, RankedTower (chartBase (a : ℤ)) (chartHead (a : ℤ)) (i a))
      (hr : ∀ a, i a ≤ r a),
      ∀ a : ℕ, ∃ φ : CMfd.of (n := 2) (leftLink a)
          ≃ₘ⟮𝓘(ℂ,ComplexModel 2),𝓘(ℂ,ComplexModel 2)⟯ CMfd.of (n := 2) (rightLink a),
        ∃ χ : CMfd.of (n := 2) (openPreimage
            (.step (chartHead (a : ℤ)) (chartCentre (a : ℤ)) (chartLast (a : ℤ)) (chartLast_blowup _))
            (leftLink a)) ≃ₘ⟮𝓘(ℂ,ComplexModel 2),𝓘(ℂ,ComplexModel 2)⟯
          CMfd.of (n := 2) (openPreimage
            (.step (chartHead ((a+1 : ℕ) : ℤ)) (chartCentre _) (chartLast _) (chartLast_blowup _))
            (rightLink a)),
        OccupiedComparison φ
          ((RankedTower.step (D a) (hr a) (chartLast_blowup _)).restrict (leftLink a))
          ((RankedTower.step (D (a+1)) (hr (a+1)) (chartLast_blowup _)).restrict (rightLink a)) χ := by
  apply no_synchronized_clock_on_unbounded_terminal_overlap_chain
    (fun a => chartHead (a : ℤ)) (fun a => chartCentre (a : ℤ)) (fun a => chartLast (a : ℤ))
    (fun a => chartLast_blowup (a : ℤ)) leftLink rightLink
  · intro a
    apply horizontal_trace_nonempty _ _ inf_le_left
    exact adjacent_horizontal_overlap (a : ℤ)
  · intro a
    apply horizontal_trace_nonempty _ _ inf_le_right
    exact adjacent_horizontal_overlap (a : ℤ)
  · intro a
    exact ⟨a,by rw [chartHead,strip_incoming_count]; rfl⟩

end
end Hironaka.HironakaG8CartierStripModel
