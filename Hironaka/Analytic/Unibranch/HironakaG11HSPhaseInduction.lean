import Hironaka.Analytic.Unibranch.HironakaG11StrictTransformTowers
import Hironaka.Analytic.Unibranch.OriginalCompactIntrinsicHSProfiles
import Mathlib.Data.Multiset.DershowitzManna

/-!
# G11 from Hilbert–Samuel phase data and Bennett's stabilization (goal G11, route steps 1–5)

The reduction of `g11:general` (`CompactSingularCentreResolution`) to its two open inputs on the
Hilbert–Samuel route, (a) a route invariant whose values transport along the overlaps of the phase
windows (lane G11B's Bierstone–Milman invariant, human decision (B')) and (b) the presentation
property (3a) of the window records, plus Bennett's classical stabilization of Hilbert–Samuel
functions. Sources: Bierstone–Milman 2008 §1 ("If `a` is a maximum point of `H_{X,·}`, then the
maximal value of `H_{X,·}` decreases after desingularization of [the presentation], and Theorem 1.1
follows (using the basic properties of `H_{X,·}` above and) using functoriality"), the basic
properties (1)–(4) of the Hilbert–Samuel function there (Bennett 1970); Bierstone–Milman 2003,
Hypotheses 1.10 and Example 1.11(2).

* `originalStalkHS_openImmersion`, `originalStalkHS_isIsoOver`, `originalStalkHS_congr`: the
  Hilbert–Samuel function is invariant under open immersions and under morphisms which are
  isomorphisms over an open set (via local embeddings, `originalStalkHS_localEmbedding_eq`);
* `HSValue`, **`HSStabilization`** (named input: decreasing sequences of Hilbert–Samuel functions
  stabilize), `singHSValues` (the finite set of singular Hilbert–Samuel values of a compact space),
  `isDershowitzMannaLT_of_replace`;
* **`HSPresentation R w 𝔪 H`** (named property (3a) of a record on a window, along the canonical towers
  of `R`): cosupports in the strict transforms, Hilbert–Samuel function `≤ H` on the strict transforms,
  cosupport = the points with value `H`, which are singular; **`HSPhaseData X H`** (finitely many
  windows of one dimension with records in the domain of a route invariant with well-ordered values,
  presenting `H` (b) and transporting along the admissible overlaps (a), compact footprints, windows
  covering the singular points of value `H`);
* `hsValue_after_phase`, **`exists_phase_modification`**: one phase (the strict-transform tower of
  `HironakaG11StrictTransformTowers` along the glued canonical towers) gives a singular-centre
  modification whose singular Hilbert–Samuel values are smaller in the Dershowitz–Manna order (the
  maximal value `H` is replaced by values `< H`);
* **`compactSingularCentreResolution_of_hsPhaseData`**: `HSStabilization` and phase data for the
  lexicographically maximal singular value of every compact non-smooth space imply
  `CompactSingularCentreResolution` (well-founded induction on the Dershowitz–Manna order).

The named inputs are local statements about records, invariants and Hilbert–Samuel functions (true by
the cited literature), not statements about modifications of compact spaces; G11 is not assumed and is
not equivalent to any of them (`CompactSingularCentreResolution` says nothing about marked ideals or
invariants, so it does not give `HSPhaseData`). Blueprint: `hironaka-g11-resume-hs-phase-induction.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11HSPhaseInduction

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences
  Hironaka HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace
  HironakaG11SingularCentreModification OriginalLocalEmbeddingStalkHS
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.HomogenizedGlueingTower (strictAlong)

noncomputable section

/-! ### The Hilbert–Samuel function along open immersions and isomorphisms over opens -/

section Invariance

/-- **The Hilbert–Samuel function is invariant under open immersions** of complex spaces. -/
theorem originalStalkHS_openImmersion {A B : SourceReducedComplexSpace} (j : A ⟶ B)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (a : A.obj.left) :
    originalStalkHS B (j.hom.left.base a) = originalStalkHS A a := by
  let e := LocalEmbedding.ofPoint A a
  obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint A a
  let e' : LocalEmbedding B :=
    { dim := e.dim
      ambient := e.ambient
      carrier := e.carrier
      analytic := e.analytic
      map := e.map ≫ j.hom.left
      isOpenImmersion :=
        @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.map e.isOpenImmersion j.hom.left hj
      overPoint := by
        rw [Category.assoc, Over.w j.hom]
        exact e.overPoint }
  funext ℓ
  have h1 := originalStalkHS_localEmbedding_eq A e c ℓ
  have h2 := originalStalkHS_localEmbedding_eq B e' c ℓ
  rw [← hc]
  exact h2.trans h1.symm

/-- **The Hilbert–Samuel function is invariant under a morphism which is an isomorphism over `U`**,
at the points over `U`. -/
theorem originalStalkHS_isIsoOver {X Y : SourceReducedComplexSpace} {q : Y ⟶ X} {U : Set X.obj.left}
    (h : IsIsoOver q U) {y : Y.obj.left} (hy : q.hom.left.base y ∈ U) :
    originalStalkHS Y y = originalStalkHS X (q.hom.left.base y) := by
  obtain ⟨V, j, hj, hjr, hjq, -⟩ := h
  have hUo : IsOpen (q.hom.left.base ⁻¹' U) := by
    rw [← hjr]
    exact hj.base_open.isOpen_range
  obtain ⟨e, ⟨c, rfl⟩, hsub, -⟩ := LocalEmbedding.exists_domain (X := Y) y hUo hy
  have hrange : range e.map.base ⊆ range j.base := by
    rw [hjr]
    exact hsub
  have := hj
  have := e.isOpenImmersion
  let g := LocallyRingedSpace.IsOpenImmersion.lift j e.map hrange
  have hg : g ≫ j = e.map := LocallyRingedSpace.IsOpenImmersion.lift_fac j e.map hrange
  have hgo : LocallyRingedSpace.IsOpenImmersion g := by
    dsimp only [g, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hopen : LocallyRingedSpace.IsOpenImmersion (e.map ≫ q.hom.left) := by
    rw [← hg, Category.assoc]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ g hgo (j ≫ q.hom.left) hjq
  let e' : LocalEmbedding X :=
    { dim := e.dim
      ambient := e.ambient
      carrier := e.carrier
      analytic := e.analytic
      map := e.map ≫ q.hom.left
      isOpenImmersion := hopen
      overPoint := by
        rw [Category.assoc, Over.w q.hom]
        exact e.overPoint }
  funext ℓ
  exact (originalStalkHS_localEmbedding_eq Y e c ℓ).trans
    (originalStalkHS_localEmbedding_eq X e' c ℓ).symm

/-- The Hilbert–Samuel function along an equality of carriers. -/
theorem originalStalkHS_congr {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {A B : Set M} (h : A = B)
    (hA : IsComplexAnalyticSubset (n := n) A) (hB : IsComplexAnalyticSubset (n := n) B) (c : A) :
    originalStalkHS (ofClosedAnalytic A hA) c =
      originalStalkHS (ofClosedAnalytic B hB) (⟨c.val, h ▸ c.property⟩ : B) := by
  subst h
  rfl

end Invariance

/-! ### Hilbert–Samuel values and Bennett's stabilization -/

section Values

/-- **The Hilbert–Samuel functions** of points of reduced complex spaces, with the pointwise order. -/
abbrev HSValue : Type :=
  {f : ℕ → ℕ // ∃ (Y : SourceReducedComplexSpace) (y : Y.obj.left), originalStalkHS Y y = f}

/-- **Bennett's stabilization** (Bennett 1970; Bierstone–Milman 2008 §1, property (4) of the
Hilbert–Samuel function; Bierstone–Milman 2003, Example 1.11(2)): every decreasing sequence of
Hilbert–Samuel functions (pointwise order) stabilizes, i.e. the strict pointwise order on Hilbert–Samuel
functions is well-founded. A classical commutative-algebra fact, used here as a named input. -/
def HSStabilization : Prop :=
  WellFoundedLT HSValue

/-- The Hilbert–Samuel value of a point. -/
def hsValue (Y : SourceReducedComplexSpace) (y : Y.obj.left) : HSValue :=
  ⟨originalStalkHS Y y, Y, y, rfl⟩

/-- The Hilbert–Samuel values at the singular points. -/
def singHSSet (X : SourceReducedComplexSpace) : Set HSValue :=
  hsValue X '' intrinsicSingularLocus X.obj

theorem singHSSet_finite (X : SourceReducedComplexSpace) [CompactSpace X.obj.left] :
    (singHSSet X).Finite := by
  apply Set.Finite.of_finite_image (f := Subtype.val) _ Subtype.val_injective.injOn
  apply (OriginalCompactIntrinsicHSProfiles.original_stalk_hs_finite_range_on_compact X _
    (OriginalIntrinsicSingularLocus.isCompact_intrinsicSingularLocus X)).subset
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨x, hx, rfl⟩

/-- **The measure of a compact space**: the finite set of Hilbert–Samuel values at its singular
points. -/
def singHSValues (X : SourceReducedComplexSpace) [CompactSpace X.obj.left] : Finset HSValue :=
  (singHSSet_finite X).toFinset

theorem mem_singHSValues {X : SourceReducedComplexSpace} [CompactSpace X.obj.left] {v : HSValue} :
    v ∈ singHSValues X ↔ ∃ x ∈ intrinsicSingularLocus X.obj, hsValue X x = v := by
  rw [singHSValues, Set.Finite.mem_toFinset]
  rfl

/-- **The Dershowitz–Manna step**: if every value of `A` is a value of `B` different from `h` or is
smaller than `h`, and `h` is a value of `B`, then `A` is smaller than `B` in the Dershowitz–Manna
order. -/
theorem isDershowitzMannaLT_of_replace {α : Type*} [Preorder α] [DecidableEq α] {A B : Finset α}
    {h : α} (hB : h ∈ B) (hA : ∀ v ∈ A, (v ∈ B ∧ v ≠ h) ∨ v < h) :
    Multiset.IsDershowitzMannaLT A.val B.val := by
  refine ⟨A.val ∩ B.val, A.val - B.val, B.val - A.val, ?_, ?_, ?_, ?_⟩
  · have hh : h ∈ B.val - A.val := by
      rw [Multiset.mem_sub_of_nodup B.nodup]
      refine ⟨hB, fun hA' => ?_⟩
      rcases hA h hA' with h1 | h1
      · exact h1.2 rfl
      · exact lt_irrefl h h1
    intro h0
    rw [h0] at hh
    exact Multiset.notMem_zero h hh
  · rw [add_comm]
    exact (Multiset.sub_add_inter A.val B.val).symm
  · rw [add_comm, Multiset.inter_comm]
    exact (Multiset.sub_add_inter B.val A.val).symm
  · intro y hy
    rw [Multiset.mem_sub_of_nodup A.nodup] at hy
    refine ⟨h, ?_, ?_⟩
    · rw [Multiset.mem_sub_of_nodup B.nodup]
      refine ⟨hB, fun hA' => ?_⟩
      rcases hA h hA' with h1 | h1
      · exact h1.2 rfl
      · exact lt_irrefl h h1
    · rcases hA y hy.1 with h1 | h1
      · exact absurd h1.1 hy.2
      · exact h1

end Values

/-! ### The Hilbert–Samuel presentation property and phase data -/

section Presentation

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]

/-- **(3a) The record `𝔪` on the window `w` presents the Hilbert–Samuel value `H`** along the
canonical towers of `R` (Bierstone–Milman 1997 Thms 9.4, 9.6; Bierstone–Milman 2008 §1: a presentation
of `H_{X,·}` has the same test sequences as `(M, ∅, X, H)`): along every canonical tower `T` the cosupport
of the transformed record lies in the strict transform `C_T` of the window carrier, and at every point
`c ∈ C_T` the Hilbert–Samuel function of `C_T` is `≤ H` (pointwise; semicontinuity and Bennett's
non-increase on a window inside the semicontinuity neighbourhood of the maximal stratum), `c` lies in the
cosupport iff it equals `H`, and then `c` is a singular point (the Hilbert–Samuel function distinguishes
smooth and singular points). -/
def HSPresentation (R : ResolutionInvariant.{0} N k Λ) (w : DimEmbedding X N)
    (𝔪 : MarkedIdeal N (CMfd.of (n := N) w.ambient)) (H : ℕ → ℕ) : Prop :=
  ∀ {Y : CMfd.{0} N} (T : BlowupTower (CMfd.of (n := N) w.ambient) Y), IsCanonical 𝔪 (R.inv 𝔪) T →
    (geoTransformAlong 𝔪 T).cosupp ⊆ strictAlong T w.carrier ∧
    ∀ (hA : IsComplexAnalyticSubset (n := N) (strictAlong T w.carrier)) (c : strictAlong T w.carrier),
      originalStalkHS (ofClosedAnalytic (strictAlong T w.carrier) hA) c ≤ H ∧
      (c.val ∈ (geoTransformAlong 𝔪 T).cosupp ↔
        originalStalkHS (ofClosedAnalytic (strictAlong T w.carrier) hA) c = H) ∧
      (c.val ∈ (geoTransformAlong 𝔪 T).cosupp →
        c ∈ intrinsicSingularLocus (ofClosedAnalytic (strictAlong T w.carrier) hA).obj)

/-- **Hilbert–Samuel phase data of `X` for the value `H`** ((a) + (b)): finitely many windows of one
ambient dimension (e.g. minimal local embeddings around the maximal stratum, lane G11B's
`HironakaG11InvMinimalLocalEmbedding`), records in the domain of a route invariant with well-ordered
values (lane G11B's Bierstone–Milman invariant) which present `H` ((3a), `HSPresentation`) and
transport along the admissible overlaps ((a), `RecordsTransport` with `mapAdm`), compact footprints
covering the images of the cosupports, and windows covering the singular points with value `H`. -/
def HSPhaseData (X : SourceReducedComplexSpace) (H : ℕ → ℕ) : Prop :=
  ∃ (N k : ℕ) (Λ : Type) (_ : LinearOrder Λ) (_ : WellFoundedLT Λ)
    (R : ResolutionInvariant.{0} N k Λ) (ι : Type) (_ : Finite ι) (w : ι → DimEmbedding X N)
    (𝔪 : ∀ i, MarkedIdeal N (Amb w i)) (K : ∀ i, Set (w i).ambient),
    (∀ i, IsInvDomain k (𝔪 i)) ∧ (∀ i, IsCompact (K i)) ∧
    (∀ i (c : (w i).carrier), c.val ∈ (𝔪 i).cosupp → ∃ j, ∃ c' : (w j).carrier,
      c'.val ∈ K j ∧ (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c) ∧
    RecordsTransport R 𝔪 (mapAdm w) ∧
    (∀ i, HSPresentation R (w i) (𝔪 i) H) ∧
    ∀ x ∈ intrinsicSingularLocus X.obj, originalStalkHS X x = H →
      ∃ i, x ∈ range (w i).toLocalEmbedding.toPoint

variable {R : ResolutionInvariant.{0} N k Λ} {ι : Type*} {w : ι → DimEmbedding X N}
  {𝔪 : ∀ i, MarkedIdeal N (Amb w i)} {H : ℕ → ℕ}

theorem HSPresentation.cosupp_subset (hP : ∀ i, HSPresentation R (w i) (𝔪 i) H) (i : ι) :
    (𝔪 i).cosupp ⊆ (w i).carrier :=
  (hP i BlowupTower.refl trivial).1

theorem HSPresentation.cosuppInStrictSing (hP : ∀ i, HSPresentation R (w i) (𝔪 i) H) :
    CosuppInStrictSing R 𝔪 := fun i _ T hT =>
  ⟨(hP i T hT).1, fun hA c hc => ((hP i T hT).2 hA c).2.2 hc⟩

/-- At stage `0`, a window point lies in the cosupport iff its image has Hilbert–Samuel value `H`. -/
theorem HSPresentation.mem_cosupp_iff (hP : ∀ i, HSPresentation R (w i) (𝔪 i) H) (i : ι)
    (c : (w i).carrier) :
    c.val ∈ (𝔪 i).cosupp ↔ originalStalkHS X ((w i).toLocalEmbedding.toPoint c) = H := by
  have h := ((hP i BlowupTower.refl trivial).2 (w i).analytic c).2.1
  have hj := originalStalkHS_openImmersion (EmbeddedBlowupOverlap.chartMorphism (w i).toLocalEmbedding)
    (w i).isOpenImmersion c
  refine h.trans ?_
  rw [show originalStalkHS X ((w i).toLocalEmbedding.toPoint c) = _ from hj]
  exact Iff.rfl

/-- **The Hilbert–Samuel values after one phase.** At a singular point `y` of the final stage of the
strict-transform tower of a phase (all cosupports empty), either `y` lies over a singular point of `X`
with the same Hilbert–Samuel value, different from `H`, or its value is `< H`. -/
theorem hsValue_after_phase (hP : ∀ i, HSPresentation R (w i) (𝔪 i) H)
    (hDcov : ∀ x ∈ intrinsicSingularLocus X.obj, originalStalkHS X x = H →
      ∃ i, x ∈ range (w i).toLocalEmbedding.toPoint)
    {T : Towers w} (xs : XStage w T) (hcan : ∀ i, IsCanonical (𝔪 i) (R.inv (𝔪 i)) (T i).2)
    (hres : ∀ i, (geoTransformAlong (𝔪 i) (T i).2).cosupp = ∅)
    (hiso : IsIsoOver xs.q (cosuppImage w 𝔪)ᶜ) (y : xs.Y.obj.left)
    (hy : y ∈ intrinsicSingularLocus xs.Y.obj) :
    (xs.q.hom.left.base y ∈ intrinsicSingularLocus X.obj ∧
      originalStalkHS xs.Y y = originalStalkHS X (xs.q.hom.left.base y) ∧
      originalStalkHS X (xs.q.hom.left.base y) ≠ H) ∨
    originalStalkHS xs.Y y < H := by
  by_cases hq : xs.q.hom.left.base y ∈ cosuppImage w 𝔪
  · right
    obtain ⟨i, c, -, hcx⟩ := hq
    have hyr : y ∈ range (xs.map i).hom.left.base := by
      rw [xs.range_map i]
      exact ⟨c, hcx⟩
    obtain ⟨d, rfl⟩ := hyr
    rw [originalStalkHS_openImmersion (xs.map i) (xs.isOpenImmersion i) d]
    have h := xs.carrier_eq i
    rw [originalStalkHS_congr h (xs.analytic i) (h ▸ xs.analytic i) d]
    obtain ⟨hle, hiff, -⟩ := (hP i (T i).2 (hcan i)).2 (h ▸ xs.analytic i) ⟨d.val, h ▸ d.property⟩
    refine lt_of_le_of_ne hle fun heq => ?_
    have hmem := hiff.mpr heq
    rw [hres i] at hmem
    exact hmem
  · left
    have hyU : xs.q.hom.left.base y ∈ (cosuppImage w 𝔪)ᶜ := hq
    refine ⟨fun hreg => hy ((hiso.mem_intrinsicRegularLocus_iff hyU).mpr hreg),
      originalStalkHS_isIsoOver hiso hyU, fun heq => hq ?_⟩
    have hsing : xs.q.hom.left.base y ∈ intrinsicSingularLocus X.obj :=
      fun hreg => hy ((hiso.mem_intrinsicRegularLocus_iff hyU).mpr hreg)
    obtain ⟨i, c, hc⟩ := hDcov _ hsing heq
    refine ⟨i, c, (HSPresentation.mem_cosupp_iff hP i c).mpr ?_, hc⟩
    rw [hc]
    exact heq

end Presentation

/-! ### The phase induction -/

section Induction

/-- **One Hilbert–Samuel phase.** For a compact non-smooth `X` with phase data for its maximal
Hilbert–Samuel value `H` (lexicographic maximum over `Sing X`, attained at `a`), there is a
singular-centre modification `q : Y ⟶ X` (each step the blowup of a closed smooth centre in the
singular locus) with compact source, whose singular Hilbert–Samuel values are smaller than those of
`X` in the Dershowitz–Manna order (`H` is replaced by values `< H`). -/
theorem exists_phase_modification (X : SourceReducedComplexSpace) [CompactSpace X.obj.left]
    (a : X.obj.left) (ha : a ∈ intrinsicSingularLocus X.obj)
    (hdata : HSPhaseData X (originalStalkHS X a)) :
    ∃ (Y : SourceReducedComplexSpace) (q : Y ⟶ X) (_ : CompactSpace Y.obj.left),
      IsSingularCentreModification q ∧
      Multiset.IsDershowitzMannaLT (singHSValues Y).val (singHSValues X).val := by
  classical
  obtain ⟨N, k, Λ, _, _, R, ι, _, w, 𝔪, K, hD, hK, hcover, hTr, hP, hDcov⟩ := hdata
  obtain ⟨m, T, xs, -, hcan, hres, -, hiso⟩ :=
    exists_resolving_strictTransform_tower hD (HSPresentation.cosupp_subset hP) hcover hTr hK
      (HSPresentation.cosuppInStrictSing hP)
  have : CompactSpace xs.Y.obj.left := xs.isSingularCentreModification.source_compact
  refine ⟨xs.Y, xs.q, inferInstance, xs.isSingularCentreModification, ?_⟩
  refine isDershowitzMannaLT_of_replace (h := hsValue X a) (mem_singHSValues.mpr ⟨a, ha, rfl⟩) ?_
  intro v hv
  obtain ⟨y, hy, rfl⟩ := mem_singHSValues.mp hv
  rcases hsValue_after_phase hP hDcov xs hcan (fun i => (hres i).2) hiso y hy with
    ⟨hs, heq, hne⟩ | hlt
  · left
    refine ⟨mem_singHSValues.mpr ⟨_, hs, Subtype.ext heq.symm⟩, fun h => hne ?_⟩
    rw [← heq]
    exact congrArg Subtype.val h
  · right
    exact hlt

/-- **G11 from Hilbert–Samuel phase data and Bennett's stabilization.** If every compact non-smooth
`X` has phase data ((a) transport of a route invariant, (b) the presentation property (3a)) for its
lexicographically maximal singular Hilbert–Samuel value, and decreasing sequences of Hilbert–Samuel
functions stabilize, then every compact reduced complex space has a resolution by finitely many
blowups with smooth centres in the singular loci (`g11:general`). -/
theorem compactSingularCentreResolution_of_hsPhaseData (hS : HSStabilization)
    (hP : ∀ (X : SourceReducedComplexSpace) [CompactSpace X.obj.left], ¬X.IsSmooth →
      ∀ a ∈ intrinsicSingularLocus X.obj,
        (∀ x ∈ intrinsicSingularLocus X.obj,
          toLex (originalStalkHS X x) ≤ toLex (originalStalkHS X a)) →
        HSPhaseData X (originalStalkHS X a)) :
    CompactSingularCentreResolution := by
  have : WellFoundedLT HSValue := hS
  suffices h : ∀ (M : Multiset HSValue) (X : SourceReducedComplexSpace) [CompactSpace X.obj.left],
      (singHSValues X).val = M → HasSingularCentreResolution X by
    intro X hX
    exact h _ X rfl
  intro M
  induction M using (Multiset.wellFounded_isDershowitzMannaLT (α := HSValue)).induction with
  | _ M ih =>
    intro X _ hXM
    by_cases hsm : X.IsSmooth
    · exact hasSingularCentreResolution_of_isSmooth hsm
    obtain ⟨a, ha, hmax⟩ :=
      OriginalCompactIntrinsicHSProfiles.exists_original_compact_singular_hs_lex_maximum X hsm
    obtain ⟨Y, q, _, hq, hlt⟩ := exists_phase_modification X a ha (hP X hsm a ha hmax)
    rw [hXM] at hlt
    exact (ih _ hlt Y rfl).of_comp hq

end Induction

end

end Hironaka.Analytic.Unibranch.HironakaG11HSPhaseInduction
