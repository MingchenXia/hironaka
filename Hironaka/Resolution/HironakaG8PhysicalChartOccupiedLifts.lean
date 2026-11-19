import Hironaka.Resolution.HironakaG8NestedOccupiedSlotComparison

/-! The physical atlas supplies coherent occupied lifts on nested charts. -/
set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8PhysicalChartOccupiedLifts
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3EmptyAwareHistory BlowupTowerIsomorphism MaxLocusLocal
  HironakaG3RTowerClass HironakaOriginalTerminalOverlapComparison
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8NestedOccupiedSlotComparison HironakaBaseChange G3UniversePhysicalClassComparisons

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}

private theorem full_open_equiv (A : CMfd.{0} n) (U : Opens A) (hU : ∀ x : A, x ∈ U) :
    ∃ e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U,
      ∀ x : A, (e x).val = x := by
  let e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U := {
    toFun x := ⟨x,hU x⟩
    invFun := Subtype.val
    left_inv _ := rfl
    right_inv _ := rfl
    contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk contMDiff_id hU
    contMDiff_invFun := contMDiff_subtype_val }
  exact ⟨e,fun _ => rfl⟩

private theorem full_restriction_iso {A B : CMfd.{0} n} (T : BlowupTower A B)
    (U : Opens A) (hU : ∀ x : A, x ∈ U) :
    ∃ e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U,
      (∀ x : A, (e x).val = x) ∧
      ∃ η : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U),
        (∀ y : B, (η y).val = y) ∧ IsTowerIso e T (restrict U T) η := by
  induction T with
  | refl =>
    obtain ⟨e,he⟩ := full_open_equiv A U hU
    exact ⟨e,he,e,he,.refl⟩
  | @step B D T C π hπ ih =>
    obtain ⟨e,he,χ,hχ,hIso⟩ := ih
    let V := openPreimage (.step T C π hπ) U
    obtain ⟨η,hη⟩ := full_open_equiv D V (fun z => hU (T.proj (π z)))
    refine ⟨e,he,η,hη,IsTowerIso.step hIso _ _ η ?_ ?_⟩
    · intro z
      apply Subtype.ext
      change π (η z).val = (χ (π z)).val
      rw [hη,hχ]
    · ext z
      change (χ z).val ∈ C ↔ z ∈ C
      rw [hχ]

/-- On nested actual charts, the full earlier physical tower compares to
the literal restriction of the later one, over the very same base points. -/
theorem physical_comparison_nested_chart (cmp : HasPhysicalComparisons K)
    (c d : TowerChart K Z P) (h : c.U ≤ d.U) :
    let U := nestedOpens d.U (c.U ⊓ d.U)
    ∃ e : CMfd.of (n := n) c.U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U,
      (∀ x : c.U, (e x).val.val = x.val) ∧
      ∃ η : c.Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage d.T U),
        EmptyAwareTowerIso e c.T (restrict U d.T) η := by
  have hComp := cmp c.U d.U c.Y d.Y c.T d.T c.mem d.mem
  obtain ⟨β,hβ⟩ := hComp
  obtain ⟨α,hα,χ,_,hχ⟩ := full_restriction_iso c.T (nestedOpens c.U (c.U ⊓ d.U))
    (fun x => ⟨x.property,h x.property⟩)
  let e := α.trans (overlapBaseEquiv (n := n)
    (inf_le_left : c.U ⊓ d.U ≤ c.U) inf_le_right)
  refine ⟨e,?_,χ.trans β,?_⟩
  · intro x
    change ((overlapBaseEquiv (n := n)
      (inf_le_left : c.U ⊓ d.U ≤ c.U) inf_le_right (α x)).val).val = x.val
    rw [overlapBaseEquiv_point,hα]
  · exact G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hχ) hβ

private abbrev chartOverlap (c d : TowerChart K Z P) : Opens d.U :=
  nestedOpens d.U (c.U ⊓ d.U)

private def chosenBase (cmp : HasPhysicalComparisons K)
    (c d : TowerChart K Z P) (h : c.U ≤ d.U) :
    CMfd.of (n := n) c.U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (chartOverlap c d) :=
  (physical_comparison_nested_chart cmp c d h).choose

private theorem chosenBase_point (cmp : HasPhysicalComparisons K)
    (c d : TowerChart K Z P) (h : c.U ≤ d.U) (x : c.U) :
    (chosenBase cmp c d h x).val.val = x.val :=
  (physical_comparison_nested_chart cmp c d h).choose_spec.1 x

private def chosenEndpoint (cmp : HasPhysicalComparisons K)
    (c d : TowerChart K Z P) (h : c.U ≤ d.U) :
    c.Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage d.T (chartOverlap c d)) :=
  (physical_comparison_nested_chart cmp c d h).choose_spec.2.choose

private theorem chosenComparison (cmp : HasPhysicalComparisons K)
    (c d : TowerChart K Z P) (h : c.U ≤ d.U) :
    EmptyAwareTowerIso (chosenBase cmp c d h) c.T
      (restrict (chartOverlap c d) d.T) (chosenEndpoint cmp c d h) :=
  (physical_comparison_nested_chart cmp c d h).choose_spec.2.choose_spec

/-- The canonical occupied lift coming from the actual nested chart comparison. -/
def chartOccupiedLift (cmp : HasPhysicalComparisons K)
    (c d : TowerChart K Z P) (h : c.U ≤ d.U) :
    {i // Occupied c.T i} ↪o {i // Occupied d.T i} :=
  occupiedLiftOnOpen (chartOverlap c d) d.T (chosenComparison cmp c d h)

theorem chartOccupiedLift_comp (cmp : HasPhysicalComparisons K)
    (a b c : TowerChart K Z P) (hab : a.U ≤ b.U) (hbc : b.U ≤ c.U) :
    (chartOccupiedLift cmp a b hab).trans (chartOccupiedLift cmp b c hbc) =
      chartOccupiedLift cmp a c (hab.trans hbc) := by
  have hDV : chartOverlap a c ≤ chartOverlap b c := by
    intro x hx
    exact ⟨hab hx.1,hx.2⟩
  have hU : (chartOverlap a b : Set b.U) =
      (Subtype.val ∘ chosenBase cmp b c hbc) ⁻¹' (chartOverlap a c : Set c.U) := by
    ext x
    change x.val ∈ a.U ⊓ b.U ↔ (chosenBase cmp b c hbc x).val.val ∈ a.U ⊓ c.U
    rw [chosenBase_point]
    exact ⟨fun h => ⟨h.1,hbc h.2⟩,fun h => ⟨h.1,hab h.1⟩⟩
  exact occupiedLiftOnOpen_comp_nested b.T c.T
    (chartOverlap a b) (chartOverlap b c) (chartOverlap a c) hDV
    (chosenComparison cmp a b hab) (chosenComparison cmp b c hbc)
    (chosenComparison cmp a c (hab.trans hbc)) hU

theorem chartOccupiedLift_id (cmp : HasPhysicalComparisons K) (c : TowerChart K Z P) :
    chartOccupiedLift cmp c c le_rfl = (OrderIso.refl _).toOrderEmbedding := by
  let e := chartOccupiedLift cmp c c le_rfl
  have h : e.trans e = e := chartOccupiedLift_comp cmp c c c le_rfl le_rfl
  ext p
  have hh : e (e p) = e p :=
    congrArg (fun q : {i // Occupied c.T i} ↪o {i // Occupied c.T i} => q p) h
  exact congrArg Subtype.val (e.injective hh)

/-- A monotone chain of actual charts supplies precisely the coherent
strictly increasing occupied lifts for the occurrence quotient. -/
theorem exists_coherent_chart_occupied_lifts (cmp : HasPhysicalComparisons K)
    (c : ℕ → TowerChart K Z P) (hMono : Monotone fun i => (c i).U) :
    ∃ up : ∀ {i j : ℕ}, i ≤ j → {k // Occupied (c i).T k} → {k // Occupied (c j).T k},
      (∀ i (p : {k // Occupied (c i).T k}), up (le_refl i) p = p) ∧
      (∀ {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) p,
        up hjk (up hij p) = up (hij.trans hjk) p) ∧
      (∀ {i j : ℕ} (hij : i ≤ j), StrictMono (up hij)) := by
  let f {i j : ℕ} (h : i ≤ j) := chartOccupiedLift cmp (c i) (c j) (hMono h)
  refine ⟨(fun {i j} h p => (f (i := i) (j := j) h) p),?_,?_,
    fun {i j} h => (f (i := i) (j := j) h).strictMono⟩
  · intro i p
    exact congrArg (fun e => e p) (chartOccupiedLift_id cmp (c i))
  · intro i j k hij hjk p
    exact congrArg (fun e => e p) (chartOccupiedLift_comp cmp (c i) (c j) (c k) (hMono hij) (hMono hjk))


end
end Hironaka.HironakaG8PhysicalChartOccupiedLifts
