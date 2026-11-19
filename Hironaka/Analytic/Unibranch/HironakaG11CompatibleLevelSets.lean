import Hironaka.Analytic.Unibranch.HironakaG11CompatibleAnalyticCover
import Hironaka.Invariant.ResolutionDriver

/-!
# Compatible level sets of local invariants (goal G11, interface of route steps 2–4 to step 1)

The canonical centre of one window is the MAXIMUM locus of the invariant on the window's
cosupport; maximum loci of different windows need not agree on overlaps. What glues is the LEVEL
SET of the invariant at the GLOBAL maximum value `λ`: if the cosupports agree on overlaps and the
invariant VALUES agree on overlaps, the level sets `{y ∈ D i | g i y = λ}` are compatible
(`isCompatible_levelSet`), and when `λ` bounds all values each level set is either empty or the
window's own maximum locus (`levelSet_eq_empty_or_eq_maxLocus`), hence a closed submanifold
whenever the window's maximum locus is one (`isClosedSubmanifold_levelSet`). For finitely many
windows whose nonempty cosupports carry a maximum, a global maximum value exists
(`exists_global_max`). `LocalSmoothCentres.compatible_of_levelSet` packages this for the gluing
interface of `HironakaG11CompatibleAnalyticCover`.

Blueprint: `hironaka-g11-resume-compatible-centres.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG11CompatibleLevelSets

open Hironaka.BlowupSequences Hironaka
  ResolutionDriver HironakaG11CompatibleAnalyticCover OriginalAnalyticClosedSubspaceSmoothCentres

noncomputable section

variable {Λ : Type*}

section Sets

variable {ι : Type*} {α : Type*} {β : ι → Type*}
  {f : ∀ i, β i → α} {D : ∀ i, Set (β i)}

/-- **Level sets glue.** Local functions on compatible local domains whose VALUES agree on
overlaps have compatible preimages of every set of values (in particular compatible level sets). -/
theorem isCompatible_levelSet (hD : IsCompatible f D) (g : ∀ i, β i → Λ)
    (hg : ∀ i k (y : β i) (z : β k), f i y = f k z → y ∈ D i → g i y = g k z) (T : Set Λ) :
    IsCompatible f (fun i => D i ∩ g i ⁻¹' T) := by
  intro i k y z hyz hy
  refine ⟨hD i k y z hyz hy.1, ?_⟩
  change g k z ∈ T
  rw [← hg i k y z hyz hy.1]
  exact hy.2

/-- **Level sets glue (overlap form).** The one-directional form produced by transport lemmas
along overlaps (e.g. `HironakaG11InvTransport.inv_eq_on_overlap`): a point of the domain of one
window whose image is seen by another window lies in that window's domain, with the SAME value.
Then all preimages of values are compatible. -/
theorem isCompatible_levelSet_of_overlap (g : ∀ i, β i → Λ)
    (hDg : ∀ i k (y : β i) (z : β k), f i y = f k z → y ∈ D i → z ∈ D k ∧ g k z = g i y)
    (T : Set Λ) : IsCompatible f (fun i => D i ∩ g i ⁻¹' T) := by
  intro i k y z hyz hy
  obtain ⟨hz, hgz⟩ := hDg i k y z hyz hy.1
  refine ⟨hz, ?_⟩
  change g k z ∈ T
  rw [hgz]
  exact hy.2

/-- The overlap form also gives compatibility of the domains themselves (e.g. cosupports). -/
theorem isCompatible_of_overlap (g : ∀ i, β i → Λ)
    (hDg : ∀ i k (y : β i) (z : β k), f i y = f k z → y ∈ D i → z ∈ D k ∧ g k z = g i y) :
    IsCompatible f D :=
  fun i k y z hyz hy => (hDg i k y z hyz hy).1

variable [LinearOrder Λ]

/-- **The level set at an upper bound is empty or the maximum locus.** -/
theorem levelSet_eq_empty_or_eq_maxLocus {γ : Type*} (s : Set γ) (g : γ → Λ) (lam : Λ)
    (hlam : ∀ y ∈ s, g y ≤ lam) :
    s ∩ g ⁻¹' {lam} = ∅ ∨ s ∩ g ⁻¹' {lam} = maxLocus g s := by
  rcases (s ∩ g ⁻¹' {lam}).eq_empty_or_nonempty with h | ⟨y₀, hy₀s, hy₀⟩
  · exact Or.inl h
  · right
    have hy₀' : g y₀ = lam := hy₀
    ext y
    constructor
    · rintro ⟨hys, hy⟩
      have hy' : g y = lam := hy
      exact ⟨hys, fun z hz => hy' ▸ hlam z hz⟩
    · rintro ⟨hys, hmax⟩
      refine ⟨hys, ?_⟩
      change g y = lam
      exact le_antisymm (hlam y hys) (hy₀' ▸ hmax y₀ hy₀s)

/-- The level set at an upper bound is contained in the maximum locus. -/
theorem levelSet_subset_maxLocus {γ : Type*} (s : Set γ) (g : γ → Λ) (lam : Λ)
    (hlam : ∀ y ∈ s, g y ≤ lam) : s ∩ g ⁻¹' {lam} ⊆ maxLocus g s := by
  rcases levelSet_eq_empty_or_eq_maxLocus s g lam hlam with h | h
  · rw [h]
    exact empty_subset _
  · exact h.le

/-- **The level set at an upper bound is a closed submanifold** as soon as the maximum locus is
one (the empty set is a closed submanifold). -/
theorem isClosedSubmanifold_levelSet {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Hironaka.ComplexModel n) M] (s : Set M) (g : M → Λ)
    (lam : Λ) (hlam : ∀ y ∈ s, g y ≤ lam) (hmax : IsClosedSubmanifold n (maxLocus g s)) :
    IsClosedSubmanifold n (s ∩ g ⁻¹' {lam}) := by
  rcases levelSet_eq_empty_or_eq_maxLocus s g lam hlam with h | h
  · rw [h]
    exact ⟨isClosed_empty, fun x hx => hx.elim⟩
  · rw [h]
    exact hmax

/-- **A global maximum value over finitely many windows.** If every nonempty local domain has a
nonempty maximum locus and some domain is nonempty, there is a value bounding all local values and
attained in some window. -/
theorem exists_global_max [Finite ι] (g : ∀ i, β i → Λ)
    (hmax : ∀ i, (D i).Nonempty → (maxLocus (g i) (D i)).Nonempty) (hne : ∃ i, (D i).Nonempty) :
    ∃ lam : Λ, (∀ i, ∀ y ∈ D i, g i y ≤ lam) ∧ ∃ i, ∃ y ∈ D i, g i y = lam := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨i₀, hi₀⟩ := hne
  let s : Finset ι := Finset.univ.filter fun i => (D i).Nonempty
  have hs : s.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
  let v : ι → Λ := fun i =>
    if h : (D i).Nonempty then g i (hmax i h).choose else g i₀ (hmax i₀ hi₀).choose
  have hv : ∀ i (h : (D i).Nonempty), v i = g i (hmax i h).choose := fun i h => dif_pos h
  obtain ⟨j, hjs, hj⟩ := s.exists_max_image v hs
  refine ⟨v j, fun i y hy => ?_, j, ?_⟩
  · have hne_i : (D i).Nonempty := ⟨y, hy⟩
    have his : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne_i⟩
    have h1 : g i y ≤ v i := by
      rw [hv i hne_i]
      exact (hmax i hne_i).choose_spec.2 y hy
    exact h1.trans (hj i his)
  · have hjne : (D j).Nonempty := (Finset.mem_filter.mp hjs).2
    exact ⟨(hmax j hjne).choose, (hmax j hjne).choose_spec.1, (hv j hjne).symm⟩

end Sets

/-- **Compatible local smooth centres from level sets.** If the local centres of a family are the
`λ`-level sets of local invariants on local domains, the domains agree on overlaps in `X` and the
invariant values agree on overlaps, the family is compatible. -/
theorem _root_.Hironaka.Analytic.Unibranch.HironakaG11CompatibleAnalyticCover.LocalSmoothCentres.compatible_of_levelSet
    {X : SourceReducedComplexSpace} {ι : Type*}
    (F : LocalSmoothCentres X ι) (D : ∀ i, Set (F.window i)) (g : ∀ i, F.window i → Λ)
    (lam : Λ) (hcentre : ∀ i, F.centre i = D i ∩ g i ⁻¹' {lam})
    (hD : IsCompatible (fun i => (F.windowMap i).hom.left.base)
      (fun i => (Subtype.val : F.windowCarrier i → F.window i) ⁻¹' D i))
    (hg : ∀ i k (y : F.windowCarrier i) (z : F.windowCarrier k),
      (F.windowMap i).hom.left.base y = (F.windowMap k).hom.left.base z → y.val ∈ D i →
        g i y.val = g k z.val) :
    F.Compatible := by
  have h := isCompatible_levelSet hD (fun i (y : F.windowCarrier i) => g i y.val) hg {lam}
  intro i k y z hyz hy
  have hy' : y.val ∈ D i ∩ g i ⁻¹' {lam} := by
    rw [← hcentre i]
    exact hy
  have hz := h i k y z hyz hy'
  change z.val ∈ F.centre k
  rw [hcentre k]
  exact hz

/-- **Compatible local smooth centres from level sets (overlap form)**, in the shape produced by
the transport lemmas: if a domain point of window `i` seen in window `k` is a domain point there
with the same invariant value, the `λ`-level-set centres are compatible. -/
theorem _root_.Hironaka.Analytic.Unibranch.HironakaG11CompatibleAnalyticCover.LocalSmoothCentres.compatible_of_levelSet_overlap
    {X : SourceReducedComplexSpace}
    {ι : Type*} (F : LocalSmoothCentres X ι) (D : ∀ i, Set (F.window i))
    (g : ∀ i, F.window i → Λ) (lam : Λ) (hcentre : ∀ i, F.centre i = D i ∩ g i ⁻¹' {lam})
    (hDg : ∀ i k (y : F.windowCarrier i) (z : F.windowCarrier k),
      (F.windowMap i).hom.left.base y = (F.windowMap k).hom.left.base z → y.val ∈ D i →
        z.val ∈ D k ∧ g k z.val = g i y.val) :
    F.Compatible := by
  apply F.compatible_of_levelSet D g lam hcentre
  · exact isCompatible_of_overlap (fun i (y : F.windowCarrier i) => g i y.val) hDg
  · intro i k y z hyz hy
    exact (hDg i k y z hyz hy).2.symm

section LevelSetFamily

variable [LinearOrder Λ]

/-- **Local smooth centres as level sets at a global bound.** Windows `(emb i, window i)`, local
domains `D i` (e.g. cosupports) inside the carriers, local invariants `g i` bounded by `λ` on
`D i`, whose maximum loci are closed submanifolds (e.g. canonical centres): the centres are the
`λ`-level sets (each empty or the window's own maximum locus). -/
def LocalSmoothCentres.ofLevelSets {X : SourceReducedComplexSpace} {ι : Type*}
    (emb : ι → LocalEmbedding X) (window : ∀ i, Opens (emb i).ambient)
    (D : ∀ i, Set (window i)) (g : ∀ i, window i → Λ) (lam : Λ)
    (hlam : ∀ i, ∀ y ∈ D i, g i y ≤ lam)
    (hmax : ∀ i, IsClosedSubmanifold (emb i).dim (maxLocus (g i) (D i)))
    (hDW : ∀ i, D i ⊆ (Subtype.val : window i → (emb i).ambient) ⁻¹' (emb i).carrier) :
    LocalSmoothCentres X ι where
  emb := emb
  window := window
  centre i := D i ∩ g i ⁻¹' {lam}
  isClosedSubmanifold i := isClosedSubmanifold_levelSet (D i) (g i) lam (hlam i) (hmax i)
  centre_subset i := inter_subset_left.trans (hDW i)

/-- **The level-set family is compatible** as soon as domains and values agree on overlaps in the
overlap form of the transport lemmas. -/
theorem LocalSmoothCentres.ofLevelSets_compatible {X : SourceReducedComplexSpace} {ι : Type*}
    (emb : ι → LocalEmbedding X) (window : ∀ i, Opens (emb i).ambient)
    (D : ∀ i, Set (window i)) (g : ∀ i, window i → Λ) (lam : Λ)
    (hlam : ∀ i, ∀ y ∈ D i, g i y ≤ lam)
    (hmax : ∀ i, IsClosedSubmanifold (emb i).dim (maxLocus (g i) (D i)))
    (hDW : ∀ i, D i ⊆ (Subtype.val : window i → (emb i).ambient) ⁻¹' (emb i).carrier)
    (hDg : ∀ i k (y : (Subtype.val : window i → (emb i).ambient) ⁻¹' (emb i).carrier)
      (z : (Subtype.val : window k → (emb k).ambient) ⁻¹' (emb k).carrier),
      (givenWindowMorphism (emb i) (window i)).hom.left.base y =
          (givenWindowMorphism (emb k) (window k)).hom.left.base z → y.val ∈ D i →
        z.val ∈ D k ∧ g k z.val = g i y.val) :
    (LocalSmoothCentres.ofLevelSets emb window D g lam hlam hmax hDW).Compatible :=
  (LocalSmoothCentres.ofLevelSets emb window D g lam hlam hmax hDW).compatible_of_levelSet_overlap
    D g lam (fun _ => rfl) hDg

/-- The centres of the level-set family are contained in the maximum loci. -/
theorem LocalSmoothCentres.ofLevelSets_centre_subset_maxLocus {X : SourceReducedComplexSpace}
    {ι : Type*} (emb : ι → LocalEmbedding X) (window : ∀ i, Opens (emb i).ambient)
    (D : ∀ i, Set (window i)) (g : ∀ i, window i → Λ) (lam : Λ)
    (hlam : ∀ i, ∀ y ∈ D i, g i y ≤ lam)
    (hmax : ∀ i, IsClosedSubmanifold (emb i).dim (maxLocus (g i) (D i)))
    (hDW : ∀ i, D i ⊆ (Subtype.val : window i → (emb i).ambient) ⁻¹' (emb i).carrier) (i : ι) :
    (LocalSmoothCentres.ofLevelSets emb window D g lam hlam hmax hDW).centre i ⊆
      maxLocus (g i) (D i) :=
  levelSet_subset_maxLocus (D i) (g i) lam (hlam i)

end LevelSetFamily

end

end Hironaka.Analytic.Unibranch.HironakaG11CompatibleLevelSets

