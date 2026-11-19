import Hironaka.Analytic.Unibranch.HironakaG11VanishingWindows
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Analytic.Unibranch.CompactOriginalEmbeddingCover

/-!
# Embedding-independent canonical principalization of the vanishing-ideal records (goal G11)

The vanishing-ideal route of the human decision I-1296 C-0001 (run in parallel with the
Hilbert--Samuel records), carried through ALL stages: for finitely many windows of one ambient
dimension (local embeddings `w i` of `X`, carriers `C_i ⊆ Ω_i ⊆ ℂ^N`), the canonical towers of the
vanishing-ideal records `(Ω_i, [], 𝓘_{C_i}, 1)` are built SIMULTANEOUSLY: at every stage each window
blows up the level set of the COMMON maximum of the values (empty on windows where it is not
attained; canonical towers allow empty steps). Sources: Włodarczyk 2005, Proposition `pr:resol` and
§2.4 (functoriality of the canonical resolution for étale maps); Bierstone--Milman 1997, §13 (the
invariant takes finitely many values over relatively compact sets).

* `exists_isTowerIso_step`: an isomorphism of towers extends over blowups of corresponding centres;
* `restrictEquiv_vanishing_overlap`, `valueSet_preimage_on_overlap`: on the overlap of two windows
  (any biholomorphism `Φ : U' ≅ U` carrying carrier to carrier) the points of the cosupports with
  values in a given set correspond under the tower isomorphism (G11B's `levelSet_preimage_on_overlap`);
* `exists_overlap_diffeo`: G11B's ambient biholomorphism of two windows of one dimension, as a
  biholomorphism of open subsets of the ambient windows;
* `Stage m`: towers over all windows, of length `m`, canonical, and compatible over EVERY ambient
  biholomorphism (`TowersCompatible`); `Stage.zero`, **`Stage.next`** (blow up the glued centres
  `centre`: the points whose value bounds all footprint values `footValues`), `stage`;
* **`value_mem_footValues`**: every value on every window is a value over a compact footprint (overlap
  biholomorphisms + compatibility), so `exists_isGreatest_footValues` (finitely many windows, compact
  footprints, proper towers, upper semicontinuous values) gives the common maximum, and
  `centre_eq_empty_or_maxLocus`: the glued centre on each window is empty or its maximum locus;
* `value_next_lt`, **`exists_stage_cosupp_eq_empty`**: the common maximum strictly drops, so in a
  well-founded order of values all cosupports become empty;
* **`exists_compatible_principalization`** (finitely many windows with compact footprints covering
  `X`) and **`exists_embeddingIndependent_principalization`** (compact `X`, the canonical invariant
  `CanonicalCentres.canonicalInvariant N`): canonical towers of the vanishing-ideal records of a
  finite cover of `X` by windows of one dimension, all of one length, each a resolution of its record
  (so `T_i^* 𝓘_{C_i} = 𝒪(-E_{T_i})`), isomorphic over every ambient biholomorphism of the windows
  carrying carrier to carrier; `exists_overlap_tower_iso`: at two window points with the same image
  in `X`, such a biholomorphism exists and the values agree over it;
* `principalization_of_isGeoResolution`, **`exists_embeddingIndependent_principalization_snc`**: on
  every window moreover the transformed divisor has simple normal crossings,
  `supp E_{T_i} = ⋃ E = T_i⁻¹ C_i`, and `T_i` is an isomorphism over `Ω_i \ C_i`.

What this route does NOT give (and why `HironakaG11GluedInvariant.exists_isSmooth_of_window_invariants`
is not applied to it): the centres are taken in the cosupports of the controlled transforms of
`𝓘_{C_i}`, which at stages `≥ 1` can contain exceptional points off the strict transforms of `C_i`; the
centres need not lie in the singular loci of the strict transforms, the induced modifications of
`X` are blowups of non-reduced ideals in general (not singular-centre modifications), and they need
not be isomorphisms over the regular locus. Nothing here proves or assumes G11; no named
proposition is introduced. Blueprint: `hironaka-g11-resume-vanishing-principalization.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11VanishingPrincipalization

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences
  Hironaka HironakaG11VanishingWindows
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq
  MarkedIdealBiholomorphism
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.ResolutionDriver (maxLocus)
open _root_.Hironaka.HironakaG11InvTransport (vanishingRecord inv_vanishingRecord_eq_on_overlap levelSet_preimage_on_overlap
  pullback_vanishingRecord restrictEquiv_vanishingRecord)
open _root_.Hironaka.MaxLocusLocal (nestedOpens nestedOpensDiffeo)
open _root_.Hironaka.BlowupTowerIsomorphism (IsTowerIso)
open _root_.Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)

noncomputable section

/-! ### Isomorphisms of towers extend along blowups of corresponding centres -/

section TowerIso

universe u

variable {n : ℕ} {X X' : CMfd.{u} n} {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
  {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
  {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}

/-- **An isomorphism of towers extends over blowups along corresponding centres** (the blowups are
biholomorphic over the base, `BlowupUniqueness.exists_biholomorphism_over`). -/
theorem exists_isTowerIso_step (h : IsTowerIso Φ T' T χ) {Z' Z : CMfd.{u} n} {C' : Set Y'}
    {π' : Z' → Y'} (hπ' : IsBlowupAlong n C' π') {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (hCC : χ ⁻¹' C = C') :
    ∃ χ₁ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z,
      IsTowerIso Φ (.step T' C' π' hπ') (.step T C π hπ) χ₁ := by
  have hB := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse χ.contMDiff χ.symm.contMDiff
    χ.apply_symm_apply χ.symm_apply_apply hπ
  rw [hCC] at hB
  obtain ⟨e, f, he, hf, hπe, -, hfe, hef⟩ := BlowupUniqueness.exists_biholomorphism_over hπ' hB
  refine ⟨⟨⟨e, f, congrFun hfe, congrFun hef⟩, he, hf⟩, IsTowerIso.step h hπ' hπ _ (fun p => ?_) hCC⟩
  have h1 : χ.symm (π (e p)) = π' p := congrFun hπe p
  show π (e p) = χ (π' p)
  rw [← h1, χ.apply_symm_apply]

end TowerIso

/-! ### Vanishing-ideal records on overlaps -/

section Overlap

universe u

variable {n k : ℕ} {Λ : Type*} [LinearOrder Λ] (R : ResolutionInvariant.{u} n k Λ) {M M' : CMfd.{u} n}
  {C : Set M} {C' : Set M'}

/-- The vanishing-ideal records of two windows are restricted-equivalent after transport along an
ambient biholomorphism `Φ : U' ≅ U` carrying carrier to carrier. -/
theorem restrictEquiv_vanishing_overlap (h𝔫 : IsInvDomain k (vanishingRecord n C')) (U : Opens M)
    (U' : Opens M')
    (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (hΦC : ∀ p : U', ((Φ p : U) : M) ∈ C ↔ (p : M') ∈ C') :
    RestrictEquiv (MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : U → M) (vanishingRecord n C)))
      (MarkedIdeal.pullback (Subtype.val : U' → M') (vanishingRecord n C')) := by
  have hU' := InvDomainTowerAlong.isInvDomain_pullback_val U' h𝔫
  have h1 := pullback_vanishingRecord (Subtype.val : U → M)
    (HironakaBaseChange.isOpenHoloEmbedding_val (n := n) U) C
  have h2 := pullback_vanishingRecord (Subtype.val : U' → M')
    (HironakaBaseChange.isOpenHoloEmbedding_val (n := n) U') C'
  rw [h1, h2]
  refine restrictEquiv_vanishingRecord Φ (ext fun p => hΦC p) ?_
  have hc := hU'.isWellFormed.isCoherent
  rw [h2] at hc
  exact hc

/-- **Centres cut out by a set of values correspond on overlaps**: for canonical towers of the
vanishing-ideal records of two windows whose restrictions are isomorphic over `Φ`, and any set `s`
of values, a point over `U'` lies in the cosupport with value in `s` iff its image under `χ` does. -/
theorem valueSet_preimage_on_overlap (h𝔪 : IsInvDomain k (vanishingRecord n C))
    (h𝔫 : IsInvDomain k (vanishingRecord n C')) (U : Opens M) (U' : Opens M')
    (Φ : CMfd.of (n := n) U' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
    (hΦC : ∀ p : U', ((Φ p : U) : M) ∈ C ↔ (p : M') ∈ C')
    {Y' Y : CMfd.{u} n} {T' : BlowupTower M' Y'} {T : BlowupTower M Y}
    (hcan' : IsCanonical (vanishingRecord n C') (R.inv (vanishingRecord n C')) T')
    (hcan : IsCanonical (vanishingRecord n C) (R.inv (vanishingRecord n C)) T)
    {χ : CMfd.of (n := n) (openPreimage T' U') ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U)}
    (hiso : IsTowerIso Φ (restrict U' T') (restrict U T) χ) (s : Set Λ) :
    χ ⁻¹' ((Subtype.val : openPreimage T U → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong (vanishingRecord n C) T).cosupp ∧ R.inv (vanishingRecord n C) T y ∈ s}) =
      (Subtype.val : openPreimage T' U' → Y') ⁻¹'
        {y | y ∈ (geoTransformAlong (vanishingRecord n C') T').cosupp ∧
          R.inv (vanishingRecord n C') T' y ∈ s} := by
  have hEq := restrictEquiv_vanishing_overlap h𝔫 U U' Φ hΦC
  ext p
  simp only [mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨hc, hv⟩
    have hL := levelSet_preimage_on_overlap R U U' Φ h𝔪 h𝔫 hEq hcan' hcan hiso
      (R.inv (vanishingRecord n C) T (χ p))
    have hp : p ∈ χ ⁻¹' ((Subtype.val : openPreimage T U → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong (vanishingRecord n C) T).cosupp ∧
          R.inv (vanishingRecord n C) T y = R.inv (vanishingRecord n C) T (χ p)}) := ⟨hc, rfl⟩
    rw [← hL] at hp
    exact ⟨hp.1, hp.2 ▸ hv⟩
  · rintro ⟨hc, hv⟩
    have hL := levelSet_preimage_on_overlap R U U' Φ h𝔪 h𝔫 hEq hcan' hcan hiso
      (R.inv (vanishingRecord n C') T' p)
    have hp : p ∈ (Subtype.val : openPreimage T' U' → Y') ⁻¹'
        {y | y ∈ (geoTransformAlong (vanishingRecord n C') T').cosupp ∧
          R.inv (vanishingRecord n C') T' y = R.inv (vanishingRecord n C') T' p} := ⟨hc, rfl⟩
    rw [hL] at hp
    exact ⟨hp.1, hp.2 ▸ hv⟩

end Overlap

/-! ### Windows of a fixed dimension: overlap biholomorphisms -/

section Windows

variable {X : SourceReducedComplexSpace} {N : ℕ}

/-- **Ambient biholomorphism of two windows of the same dimension near points with the same image**,
as a biholomorphism of open subsets of the two ambient windows (G11B's
`HironakaG11InvLocalEmbeddingIso.exists_ambient_biholomorphism`). -/
theorem exists_overlap_diffeo (w₁ w₂ : DimEmbedding X N) (y : w₁.carrier) (z : w₂.carrier)
    (hyz : w₁.toLocalEmbedding.toPoint y = w₂.toLocalEmbedding.toPoint z) :
    ∃ (U : Opens w₁.ambient) (U' : Opens w₂.ambient)
      (Ψ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U)
      (hz : z.val ∈ U') (hy : y.val ∈ U),
      Ψ ⟨z.val, hz⟩ = ⟨y.val, hy⟩ ∧
      ∀ p : U', ((Ψ p : U) : w₁.ambient) ∈ w₁.carrier ↔ (p : w₂.ambient) ∈ w₂.carrier := by
  obtain ⟨A, B, hA, hB, Φ, hzA, hΦz, hcar, -⟩ :=
    HironakaG11InvLocalEmbeddingIso.exists_ambient_biholomorphism w₂.toLocalEmbedding
      w₁.toLocalEmbedding rfl z y hyz.symm
  let Ψ : CMfd.of (n := N) (nestedOpens w₂.ambient A) ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯
      CMfd.of (n := N) (nestedOpens w₁.ambient B) :=
    (nestedOpensDiffeo (n := N) hA).trans (Φ.trans (nestedOpensDiffeo (n := N) hB).symm)
  have hΨ : ∀ p : nestedOpens w₂.ambient A,
      (((Ψ p : nestedOpens w₁.ambient B) : w₁.ambient) : ComplexModel N) =
        (Φ ⟨((p : w₂.ambient) : ComplexModel N), p.property⟩ : ComplexModel N) := fun _ => rfl
  have hΨC : ∀ p : nestedOpens w₂.ambient A,
      ((Ψ p : nestedOpens w₁.ambient B) : w₁.ambient) ∈ w₁.carrier ↔
        (p : w₂.ambient) ∈ w₂.carrier := by
    intro p
    rw [← HironakaG11InvMinimalAmbient.val_mem_coordinateCarrier_iff w₁.carrier, hΨ,
      ← HironakaG11InvMinimalAmbient.val_mem_coordinateCarrier_iff w₂.carrier]
    exact (hcar ⟨((p : w₂.ambient) : ComplexModel N), p.property⟩).symm
  have hyB : y.val ∈ nestedOpens w₁.ambient B := by
    show ((y.val : w₁.ambient) : ComplexModel N) ∈ B
    rw [← hΦz]
    exact (Φ _).property
  refine ⟨nestedOpens w₁.ambient B, nestedOpens w₂.ambient A, Ψ, hzA, hyB, ?_, hΨC⟩
  apply Subtype.ext
  apply Subtype.ext
  rw [hΨ]
  exact hΦz

end Windows

/-! ### The glued canonical towers of finitely many windows -/

section Glue

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ] {ι : Type*}
  (R : ResolutionInvariant.{0} N k Λ) (w : ι → DimEmbedding X N)

/-- The ambient complex manifold of the `i`-th window. -/
abbrev Amb (i : ι) : CMfd.{0} N := CMfd.of (n := N) (w i).ambient

/-- One tower over every window. -/
abbrev Towers : Type _ := ∀ i, Σ Y : CMfd.{0} N, BlowupTower (Amb w i) Y

variable {w}

/-- The cosupport of the transform of the `i`-th window record along its tower. -/
abbrev cos (T : Towers w) (i : ι) : Set (T i).1 :=
  (geoTransformAlong (windowRecord (w i)) (T i).2).cosupp

/-- The value of the route invariant on the `i`-th window record along its tower. -/
abbrev value (T : Towers w) (i : ι) : (T i).1 → Λ :=
  R.inv (windowRecord (w i)) (T i).2

/-- **Compatibility over every ambient biholomorphism**: for all windows `i`, `j` and every
biholomorphism `Φ : U' ≅ U` of opens of their ambients carrying the carrier of `j` onto that of `i`,
the restricted towers are isomorphic over `Φ`. -/
def TowersCompatible (T : Towers w) : Prop :=
  ∀ (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
    (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U),
    (∀ p : U', ((Φ p : U) : (w i).ambient) ∈ (w i).carrier ↔ (p : (w j).ambient) ∈ (w j).carrier) →
    ∃ χ, IsTowerIso Φ (restrict U' (T j).2) (restrict U (T i).2) χ

variable (w)

/-- **A stage of the glued tower**: one canonical tower of the vanishing-ideal record over every
window, all of length `m`, compatible over every ambient biholomorphism. -/
structure Stage (m : ℕ) where
  /-- The towers. -/
  T : Towers w
  length : ∀ i, (T i).2.length = m
  canonical : ∀ i, IsCanonical (windowRecord (w i)) (R.inv (windowRecord (w i))) (T i).2
  compatible : TowersCompatible T

/-- Stage `0`: the empty towers. -/
def Stage.zero : Stage R w 0 where
  T i := ⟨Amb w i, .refl⟩
  length _ := rfl
  canonical _ := trivial
  compatible _ _ _ _ Φ _ := ⟨Φ, IsTowerIso.refl⟩

variable {w} (K : ∀ i, Set (w i).ambient)

/-- **The footprint values**: the values of the window records along the towers at the points of
the cosupports over the compact footprints `K i`. -/
def footValues (T : Towers w) : Set Λ :=
  ⋃ i, value R T i '' (cos T i ∩ (T i).2.proj ⁻¹' K i)

/-- **The glued centre on the `i`-th window**: the points of the cosupport whose value bounds all
footprint values (the level set of the common maximum, or empty). -/
def centre (T : Towers w) (i : ι) : Set (T i).1 :=
  {y | y ∈ cos T i ∧ value R T i y ∈ upperBounds (footValues R K T)}

theorem cosupp_windowRecord (w₀ : DimEmbedding X N) : (windowRecord w₀).cosupp = w₀.carrier :=
  SmoothCentreLocus.cosupp_vanishingIdeal w₀.analytic.isClosed (subset_univ _)

variable {R} (hD : ∀ i, IsInvDomain k (windowRecord (w i)))
  (hcover : ∀ x : X.obj.left, ∃ i, ∃ c : (w i).carrier, c.val ∈ K i ∧
    (w i).toLocalEmbedding.toPoint c = x)

include hD hcover in
/-- **Every value is a footprint value**: at a stage, the value at any point of the cosupport over
any window is attained over the footprint of some window (the overlap biholomorphisms and the
compatibility of the towers). -/
theorem value_mem_footValues {m : ℕ} (s : Stage R w m) (i : ι) (y : (s.T i).1)
    (hy : y ∈ cos s.T i) : value R s.T i y ∈ footValues R K s.T := by
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i)
  have hx : (s.T i).2.proj y ∈ (w i).carrier := by
    have h := StepOneLowerDomain.proj_mem_cosupp_of_mem_cosupp
      (hD i).isWellFormed.isClosedSubmanifold_N (hD i).isWellFormed.isCoherent _ hTt hy
    rwa [cosupp_windowRecord] at h
  obtain ⟨j, c', hc'K, hc'⟩ := hcover ((w i).toLocalEmbedding.toPoint ⟨_, hx⟩)
  obtain ⟨U, U', Ψ, hc'U', hxU, hΨc, hΨC⟩ := exists_overlap_diffeo (w i) (w j) ⟨_, hx⟩ c' hc'.symm
  obtain ⟨χ, hiso⟩ := s.compatible i j U U' Ψ hΨC
  let q : openPreimage (s.T i).2 U := ⟨y, hxU⟩
  have hχp : χ (χ.symm q) = q := χ.apply_symm_apply q
  have hp : ((χ (χ.symm q) : openPreimage (s.T i).2 U) : (s.T i).1) ∈ cos s.T i := by
    rw [hχp]
    exact hy
  obtain ⟨hpc, hpv⟩ := inv_vanishingRecord_eq_on_overlap R (hD i) (hD j) U U' Ψ hΨC
    (s.canonical j) (s.canonical i) hiso (χ.symm q) hp
  have hproj : (s.T j).2.proj (χ.symm q).val = c'.val := by
    have h1 := hiso.proj_comm (χ.symm q)
    rw [hχp] at h1
    have h2 := proj_restrict U (s.T i).2 q
    have h3 : (restrict U' (s.T j).2).proj (χ.symm q) = ⟨c'.val, hc'U'⟩ :=
      Ψ.injective (h1.trans ((show (restrict U (s.T i).2).proj q = ⟨(s.T i).2.proj y, hxU⟩ from
        Subtype.ext h2).trans hΨc.symm))
    have h4 := proj_restrict U' (s.T j).2 (χ.symm q)
    rw [h3] at h4
    exact h4.symm
  refine mem_iUnion.mpr ⟨j, (χ.symm q).val, ⟨hpc, ?_⟩, ?_⟩
  · show (s.T j).2.proj (χ.symm q).val ∈ K j
    rw [hproj]
    exact hc'K
  · change R.inv (windowRecord (w j)) (s.T j).2 (χ.symm q).val = R.inv (windowRecord (w i)) (s.T i).2 y
    rw [hpv, hχp]

include hD in
/-- **The footprint values have a greatest element** (finitely many windows, compact footprints,
proper towers, upper semicontinuous values). -/
theorem exists_isGreatest_footValues [Finite ι] (hK : ∀ i, IsCompact (K i)) {m : ℕ} (s : Stage R w m)
    (hne : (footValues R K s.T).Nonempty) : ∃ M, IsGreatest (footValues R K s.T) M := by
  have hpiece : ∀ i, (cos s.T i ∩ (s.T i).2.proj ⁻¹' K i).Nonempty →
      ∃ y ∈ cos s.T i ∩ (s.T i).2.proj ⁻¹' K i,
        ∀ y' ∈ cos s.T i ∩ (s.T i).2.proj ⁻¹' K i, value R s.T i y' ≤ value R s.T i y := by
    intro i hnei
    have hTt := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i)
    have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong (hD i) _ hTt
    have hSc : IsClosed (cos s.T i) :=
      GiraudAlong.isClosed_cosupport_along hdomT.isWellFormed.isCoherent
        hdomT.isWellFormed.isClosedSubmanifold_N _
    have hSK : IsCompact (cos s.T i ∩ (s.T i).2.proj ⁻¹' K i) :=
      ((HironakaLocalPrincipalization.isProperMap_proj (s.T i).2).isCompact_preimage (hK i)).inter_left hSc
    exact ((R.isInvValue.usc _ (hD i) _ (s.canonical i)).mono inter_subset_left).exists_isMaxOn hSK hnei
  choose f hf hfmax using hpiece
  obtain ⟨v, hv⟩ := hne
  obtain ⟨i, y, hy, -⟩ := mem_iUnion.mp hv
  have : Finite {i // (cos s.T i ∩ (s.T i).2.proj ⁻¹' K i).Nonempty} := Subtype.finite
  obtain ⟨i₀, -, hi₀⟩ := Set.exists_max_image (univ : Set {i // (cos s.T i ∩ (s.T i).2.proj ⁻¹' K i).Nonempty})
    (fun i => value R s.T i.1 (f i.1 i.2)) (Set.toFinite _) ⟨⟨i, y, hy⟩, trivial⟩
  refine ⟨value R s.T i₀.1 (f i₀.1 i₀.2), mem_iUnion.mpr ⟨i₀.1, _, hf _ _, rfl⟩, ?_⟩
  rintro v' hv'
  obtain ⟨i', y', hy', rfl⟩ := mem_iUnion.mp hv'
  exact (hfmax i' ⟨y', hy'⟩ y' hy').trans (hi₀ ⟨i', y', hy'⟩ trivial)

include hD hcover in
/-- **The glued centre is empty or the maximum locus** of the window's own invariant, so the towers
extended by the glued centres stay canonical (with empty steps allowed). -/
theorem centre_eq_empty_or_maxLocus {m : ℕ} (s : Stage R w m) (i : ι) :
    centre R K s.T i = ∅ ∨ centre R K s.T i = maxLocus (value R s.T i) (cos s.T i) := by
  rcases (centre R K s.T i).eq_empty_or_nonempty with h | ⟨y₀, hy₀c, hy₀⟩
  · exact Or.inl h
  · right
    ext y
    constructor
    · rintro ⟨hyc, hy⟩
      exact ⟨hyc, fun y' hy' => hy (value_mem_footValues K hD hcover s i y' hy')⟩
    · rintro ⟨hyc, hy⟩
      exact ⟨hyc, fun v hv => (hy₀ hv).trans (hy y₀ hy₀c)⟩

include hD hcover in
/-- The glued centre is a closed submanifold with empty interior: it can be blown up. -/
theorem exists_blowup_centre {m : ℕ} (s : Stage R w m) (i : ι) :
    ∃ (Z : CMfd.{0} N) (π : Z → (s.T i).1), IsBlowupAlong N (centre R K s.T i) π := by
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i)
  rcases centre_eq_empty_or_maxLocus K hD hcover s i with h | h
  · rw [h]
    exact ResolutionDriver.exists_blowup ∅
      (isAdmissibleCentre_empty (geoTransformAlong (windowRecord (w i)) (s.T i).2)).1 interior_empty
  · rw [h]
    exact ResolutionDriver.exists_blowup _
      (R.isInvValue.isAdmissibleCentre_maxLocus (hD i) _ (s.canonical i) hTt).1
      (ResolutionInvariantDriver.interior_maxLocus_eq_empty (hD i) _ hTt _)

/-- The space of the blowup of the glued centre over the `i`-th window. -/
def nextSpace {m : ℕ} (s : Stage R w m) (i : ι) : CMfd.{0} N :=
  (exists_blowup_centre K hD hcover s i).choose

/-- The blowup of the glued centre over the `i`-th window. -/
def nextMap {m : ℕ} (s : Stage R w m) (i : ι) : nextSpace K hD hcover s i → (s.T i).1 :=
  (exists_blowup_centre K hD hcover s i).choose_spec.choose

theorem nextMap_isBlowup {m : ℕ} (s : Stage R w m) (i : ι) :
    IsBlowupAlong N (centre R K s.T i) (nextMap K hD hcover s i) :=
  (exists_blowup_centre K hD hcover s i).choose_spec.choose_spec

/-- **The next stage of the glued tower**: blow up, over every window, the glued centre (the level
set of the common maximum of the footprint values, empty on windows where it is not attained). The
towers stay canonical, and compatible over every ambient biholomorphism (the glued centres
correspond on overlaps). -/
def Stage.next {m : ℕ} (s : Stage R w m) : Stage R w (m + 1) where
  T i := ⟨nextSpace K hD hcover s i,
    .step (s.T i).2 (centre R K s.T i) (nextMap K hD hcover s i) (nextMap_isBlowup K hD hcover s i)⟩
  length i := by
    show (s.T i).2.length + 1 = m + 1
    rw [s.length i]
  canonical i := ⟨s.canonical i, centre_eq_empty_or_maxLocus K hD hcover s i⟩
  compatible := by
    intro i j U U' Φ hΦC
    obtain ⟨χ, hiso⟩ := s.compatible i j U U' Φ hΦC
    exact exists_isTowerIso_step hiso _ _ (valueSet_preimage_on_overlap R (hD i) (hD j) U U' Φ hΦC
      (s.canonical j) (s.canonical i) hiso (upperBounds (footValues R K s.T)))

include hD hcover in
/-- **The values drop below the common maximum** after the blowup of the glued centres
(properties (3), (4) of the route invariant). -/
theorem value_next_lt {m : ℕ} (s : Stage R w m) {M : Λ} (hM : IsGreatest (footValues R K s.T) M)
    (i : ι) (z : ((s.next K hD hcover).T i).1) (hz : z ∈ cos (s.next K hD hcover).T i) :
    value R (s.next K hD hcover).T i z < M := by
  have hπ := nextMap_isBlowup K hD hcover s i
  have hTt' := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ ((s.next K hD hcover).canonical i)
  have hπz : nextMap K hD hcover s i z ∈ cos s.T i :=
    StepOneWellFounded.proj_mem_cosupp_step (hD i).isWellFormed.isClosedSubmanifold_N
      (hD i).isWellFormed.isCoherent (s.T i).2 _ _ hπ hTt' hz
  have hle : value R s.T i (nextMap K hD hcover s i z) ≤ M :=
    hM.2 (value_mem_footValues K hD hcover s i _ hπz)
  have hnotC : nextMap K hD hcover s i z ∉ centre R K s.T i →
      value R s.T i (nextMap K hD hcover s i z) < M := fun hC =>
    lt_of_le_of_ne hle fun h => hC ⟨hπz, by rw [h]; exact hM.2⟩
  change R.inv (windowRecord (w i)) (.step (s.T i).2 (centre R K s.T i) (nextMap K hD hcover s i) hπ) z < M
  by_cases hzC : nextMap K hD hcover s i z ∈ centre R K s.T i
  · have hCne : (centre R K s.T i).Nonempty := ⟨_, hzC⟩
    have hCmax := (centre_eq_empty_or_maxLocus K hD hcover s i).resolve_left hCne.ne_empty
    exact ((R.isInvValue.decrease _ (hD i) (s.T i).2 _ _ hπ (s.canonical i) hCne hCmax z hz).1
      hzC).trans_le hle
  · have heq : R.inv (windowRecord (w i)) (.step (s.T i).2 (centre R K s.T i) (nextMap K hD hcover s i) hπ) z =
        value R s.T i (nextMap K hD hcover s i z) := by
      by_cases hCne : (centre R K s.T i).Nonempty
      · have hCmax := (centre_eq_empty_or_maxLocus K hD hcover s i).resolve_left hCne.ne_empty
        exact (R.isInvValue.decrease _ (hD i) (s.T i).2 _ _ hπ (s.canonical i) hCne hCmax z hz).2 hzC
      · exact R.isInvValue.emptyStep _ (hD i) (s.T i).2 _ _ hπ (not_nonempty_iff_eq_empty.mp hCne)
          (s.canonical i) z hz
    rw [heq]
    exact hnotC hzC

variable (R) in
/-- **The stages of the glued tower**, by recursion. -/
def stage : (m : ℕ) → Stage R w m
  | 0 => Stage.zero R w
  | m + 1 => (stage m).next K hD hcover

include hD hcover in
/-- **The glued tower terminates**: at some stage every cosupport is empty. The common maximum of
the footprint values strictly drops from stage to stage (`value_next_lt`), in a well-founded order. -/
theorem exists_stage_cosupp_eq_empty [Finite ι] [WellFoundedLT Λ] (hK : ∀ i, IsCompact (K i)) :
    ∃ m, ∀ i, cos (stage R K hD hcover m).T i = ∅ := by
  by_contra hcon
  push Not at hcon
  have hne : ∀ m, (footValues R K (stage R K hD hcover m).T).Nonempty := fun m => by
    obtain ⟨i, hi⟩ := hcon m
    obtain ⟨y, hy⟩ := hi
    exact ⟨_, value_mem_footValues K hD hcover _ i y hy⟩
  choose M hM using fun m => exists_isGreatest_footValues K hD hK (stage R K hD hcover m) (hne m)
  have hlt : ∀ m, M (m + 1) < M m := by
    intro m
    obtain ⟨i, z, hz, hzM⟩ := mem_iUnion.mp (hM (m + 1)).1
    rw [← hzM]
    exact value_next_lt K hD hcover (stage R K hD hcover m) (hM m) i z hz.1
  obtain ⟨m, hm⟩ := WellFounded.not_rel_apply_succ (r := (· < ·)) M
  exact hm (hlt m)

include hD hcover in
/-- **Embedding-independent canonical principalization of the vanishing-ideal records of finitely
many windows** (general form). Let `w i` be finitely many windows of one ambient dimension `N` whose
vanishing-ideal records lie in the domain of a route invariant `R` with well-ordered values, and
`K i` compact footprints whose carrier points cover `X`. Then there are towers `T i` over the
windows, all of one length `m`, such that every `T i` is a canonical tower of the vanishing-ideal
record of `w i` (centres empty or maximum loci) and a resolution of it, so that it principalizes the
vanishing ideal of the carrier (`T_i^* 𝓘_{C_i} = 𝒪(-E_{T_i})`), and such that over EVERY
biholomorphism of opens of two ambients carrying carrier onto carrier the restricted towers are
isomorphic (`TowersCompatible`). -/
theorem exists_compatible_principalization [Finite ι] [WellFoundedLT Λ] (hK : ∀ i, IsCompact (K i)) :
    ∃ (m : ℕ) (T : Towers w),
      (∀ i, (T i).2.length = m) ∧
      (∀ i, IsCanonical (windowRecord (w i)) (R.inv (windowRecord (w i))) (T i).2) ∧
      (∀ i, IsGeoResolution (windowRecord (w i)) (T i).2) ∧
      (∀ i, GermIdeal.pullback (m := N) (T i).2.proj (vanishingIdeal (n := N) (w i).carrier) =
        (exceptionalDivisor (T i).2).ideal) ∧
      TowersCompatible T := by
  obtain ⟨m, hm⟩ := exists_stage_cosupp_eq_empty (R := R) K hD hcover hK
  set s := stage R K hD hcover m
  have hres : ∀ i, IsGeoResolution (windowRecord (w i)) (s.T i).2 := fun i =>
    ⟨R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i), hm i⟩
  refine ⟨m, s.T, s.length, s.canonical, hres, fun i => ?_, s.compatible⟩
  exact pullback_eq_exceptionalDivisor_of_isGeoResolution (windowRecord (w i)) rfl
    (hD i).isWellFormed.isCoherent rfl (s.T i).2 (hres i)

include hD in
/-- **Embedding independence at points of `X`**: for compatible canonical towers, at two window
points with the same image in `X` there is an ambient biholomorphism of neighbourhoods carrying
carrier to carrier and the first point to the second, the restricted towers are isomorphic over it,
and the values of the two vanishing-ideal records agree at corresponding points of the cosupports. -/
theorem exists_overlap_tower_iso {T : Towers w}
    (hcan : ∀ i, IsCanonical (windowRecord (w i)) (R.inv (windowRecord (w i))) (T i).2)
    (hcomp : TowersCompatible T) (i j : ι) (c : (w i).carrier) (c' : (w j).carrier)
    (hcc : (w i).toLocalEmbedding.toPoint c = (w j).toLocalEmbedding.toPoint c') :
    ∃ (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
      (Ψ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U)
      (hc' : c'.val ∈ U') (hc : c.val ∈ U), Ψ ⟨c'.val, hc'⟩ = ⟨c.val, hc⟩ ∧
      (∀ p : U', ((Ψ p : U) : (w i).ambient) ∈ (w i).carrier ↔ (p : (w j).ambient) ∈ (w j).carrier) ∧
      ∃ χ, IsTowerIso Ψ (restrict U' (T j).2) (restrict U (T i).2) χ ∧
        ∀ p : openPreimage (T j).2 U', ((χ p : openPreimage (T i).2 U) : (T i).1) ∈ cos T i →
          (p : (T j).1) ∈ cos T j ∧ value R T j p = value R T i (χ p) := by
  obtain ⟨U, U', Ψ, hc'U', hcU, hΨc, hΨC⟩ := exists_overlap_diffeo (w i) (w j) c c' hcc
  obtain ⟨χ, hiso⟩ := hcomp i j U U' Ψ hΨC
  exact ⟨U, U', Ψ, hc'U', hcU, hΨc, hΨC, χ, hiso, fun p hp =>
    inv_vanishingRecord_eq_on_overlap R (hD i) (hD j) U U' Ψ hΨC (hcan j) (hcan i) hiso p hp⟩

end Glue

/-! ### Principalization of one resolved window record -/

section WindowPrincipalization

variable {X : SourceReducedComplexSpace} {N k : ℕ}

/-- **A resolution of the vanishing-ideal record of a window principalizes the carrier**
(Włodarczyk 2005, §2.3, (1) ⟹ (2)): `T^* 𝓘_C = 𝒪(-E_T)`, the transformed divisor has simple normal
crossings, `supp E_T` is the union of its members and equals `T⁻¹ C`, and `T` is an isomorphism over
`Ω \ C`. -/
theorem principalization_of_isGeoResolution (w₀ : DimEmbedding X N)
    (hD : IsInvDomain k (windowRecord w₀)) {Y : CMfd.{0} N}
    (T : BlowupTower (CMfd.of (n := N) w₀.ambient) Y) (hres : IsGeoResolution (windowRecord w₀) T) :
    GermIdeal.pullback (m := N) T.proj (vanishingIdeal (n := N) w₀.carrier) =
        (exceptionalDivisor T).ideal ∧
      NormalCrossings.IsSNCDivisor N (geoTransformAlong (windowRecord w₀) T).E ∧
      (exceptionalDivisor T).support = ⋃ H ∈ (geoTransformAlong (windowRecord w₀) T).E, H ∧
      (exceptionalDivisor T).support = T.proj ⁻¹' w₀.carrier ∧
      IsIsomorphismOver N T.proj w₀.carrierᶜ := by
  have hpb := pullback_eq_exceptionalDivisor_of_isGeoResolution (windowRecord w₀) rfl
    hD.isWellFormed.isCoherent rfl T hres
  have hsuppC : (exceptionalDivisor T).support = T.proj ⁻¹' w₀.carrier := by
    rw [EffectiveDivisor.support, ← hpb,
      BlowupExceptionalDivisor.zeroLocus_pullback T.contMDiff_proj hD.isWellFormed.isCoherent]
    exact congrArg (T.proj ⁻¹' ·) (SmoothCentreLocus.zeroLocus_vanishingIdeal w₀.analytic.isClosed)
  refine ⟨hpb, (InvDomainTowerAlong.isInvDomain_geoTransformAlong hD T hres.1).isWellFormed.isSNCDivisor,
    HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion _ rfl T, hsuppC, ?_⟩
  refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    T.isBlowupSequence ?_
  rintro x ⟨z, hz, rfl⟩
  have hz' := HironakaPrincipalization.exceptionalLocus_subset_support T hz
  rw [hsuppC] at hz'
  exact hz'

end WindowPrincipalization

/-! ### Compact complex spaces -/

section Compact

open CompactOriginalEmbeddingCover

/-- **Embedding-independent canonical principalization of a compact complex space** (vanishing-ideal
route, G11; human decision I-1296 C-0001). Let `X` be a compact reduced complex space. There are
finitely many local embeddings `w i` of `X`, all of one ambient dimension `N`, covering `X`, with
thin carriers `C_i ⊆ Ω_i ⊆ ℂ^N`, and blowup towers `T i` of the ambient windows `Ω_i`, all of one
length `m`, such that
* each `T i` is a canonical tower of the vanishing-ideal record `(Ω_i, [], 𝓘_{C_i}, 1)` for the
  canonical resolution invariant `CanonicalCentres.canonicalInvariant N` (every centre is empty or
  the maximum locus of the invariant on the cosupport), and a resolution of it;
* `T_i` principalizes the vanishing ideal: `T_i^* 𝓘_{C_i} = 𝒪(-E_{T_i})`;
* **embedding independence**: for any two windows and EVERY biholomorphism `Φ : U' ≅ U` of open
  subsets of their ambients carrying `C_j ∩ U'` onto `C_i ∩ U`, the restricted towers are isomorphic
  over `Φ`.

What this does NOT give: the centres need not lie in the singular locus of (the strict transforms
of) `X`, the induced modification of `X` need not be an isomorphism over the regular locus, and the
strict transforms of `X` are not shown to be smooth at an intermediate stage. -/
theorem exists_embeddingIndependent_principalization (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] :
    ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (w : ι → DimEmbedding X N),
      (∀ x : X.obj.left, ∃ i, x ∈ range (w i).toLocalEmbedding.toPoint) ∧
      (∀ i, interior (w i).carrier = ∅) ∧
      ∃ (m : ℕ) (T : Towers w),
        (∀ i, (T i).2.length = m) ∧
        (∀ i, IsCanonical (windowRecord (w i))
          ((CanonicalCentres.canonicalInvariant.{0} N).inv (windowRecord (w i))) (T i).2) ∧
        (∀ i, IsGeoResolution (windowRecord (w i)) (T i).2) ∧
        (∀ i, GermIdeal.pullback (m := N) (T i).2.proj (vanishingIdeal (n := N) (w i).carrier) =
          (exceptionalDivisor (T i).2).ideal) ∧
        TowersCompatible T := by
  classical
  obtain ⟨V, s, hV, hcov, -⟩ := exists_finite_localEmbedding_shrinking X
  let e : s → LocalEmbedding X := fun x => LocalEmbedding.ofPoint X x.1
  let N := s.sup (fun x => (LocalEmbedding.ofPoint X x).dim) + 1
  have hN : ∀ i : s, (e i).dim < N := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun x => (LocalEmbedding.ofPoint X x).dim) i.2)
  let w : s → DimEmbedding X N := raisedWindows e hN
  have hrange : ∀ i : s, range (w i).toLocalEmbedding.toPoint = range (e i).toPoint := fun i =>
    DimEmbedding.range_toPoint_raise (e i) N (hN i).le
  have hsub : ∀ i : s, closure (V i.1 : Set X.obj.left) ⊆ range (w i).toLocalEmbedding.toPoint :=
    fun i => (hrange i).symm ▸ (hV i.1).2
  have hcpt : ∀ i : s, IsCompact (closure (V i.1 : Set X.obj.left)) := fun i =>
    isClosed_closure.isCompact
  let K : ∀ i : s, Set (w i).ambient := fun i =>
    Subtype.val '' ((w i).toLocalEmbedding.toPoint ⁻¹' closure (V i.1 : Set X.obj.left))
  have hK : ∀ i, IsCompact (K i) := fun i =>
    ((w i).toLocalEmbedding.isOpenEmbedding_toPoint.isEmbedding.isInducing.isCompact_preimage'
      (hcpt i) (hsub i)).image continuous_subtype_val
  have hcover : ∀ x : X.obj.left, ∃ i, ∃ c : (w i).carrier, c.val ∈ K i ∧
      (w i).toLocalEmbedding.toPoint c = x := by
    intro x
    have hx : x ∈ ⋃ y ∈ s, (V y : Set X.obj.left) := hcov ▸ mem_univ x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
    obtain ⟨c, hc⟩ := hsub ⟨y, hy⟩ (subset_closure hxy)
    exact ⟨⟨y, hy⟩, c, ⟨c, by rw [mem_preimage, hc]; exact subset_closure hxy, rfl⟩, hc⟩
  have hD : ∀ i, IsInvDomain N (windowRecord (w i)) := isInvDomain_raisedWindows le_rfl e hN
  obtain ⟨m, T, hlen, hcan, hres, hpb, hcomp⟩ :=
    exists_compatible_principalization (R := CanonicalCentres.canonicalInvariant.{0} N) K hD hcover hK
  refine ⟨N, s, inferInstance, w, fun x => ?_, fun i => DimEmbedding.interior_carrier_raise (e i) N (hN i),
    m, T, hlen, hcan, hres, hpb, hcomp⟩
  obtain ⟨i, c, -, hc⟩ := hcover x
  exact ⟨i, c, hc⟩

/-- **Embedding-independent canonical principalization of a compact complex space, with simple
normal crossings**: `exists_embeddingIndependent_principalization` together with, on every window,
the normal crossings of the transformed divisor, `supp E_{T_i} = ⋃ E = T_i⁻¹ C_i`, and `T_i` an
isomorphism over `Ω_i \ C_i` (`principalization_of_isGeoResolution`). -/
theorem exists_embeddingIndependent_principalization_snc (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] :
    ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (w : ι → DimEmbedding X N),
      (∀ x : X.obj.left, ∃ i, x ∈ range (w i).toLocalEmbedding.toPoint) ∧
      (∀ i, interior (w i).carrier = ∅) ∧
      ∃ (m : ℕ) (T : Towers w),
        (∀ i, (T i).2.length = m) ∧
        (∀ i, IsCanonical (windowRecord (w i))
          ((CanonicalCentres.canonicalInvariant.{0} N).inv (windowRecord (w i))) (T i).2) ∧
        (∀ i, IsGeoResolution (windowRecord (w i)) (T i).2) ∧
        (∀ i, GermIdeal.pullback (m := N) (T i).2.proj (vanishingIdeal (n := N) (w i).carrier) =
            (exceptionalDivisor (T i).2).ideal ∧
          NormalCrossings.IsSNCDivisor N (geoTransformAlong (windowRecord (w i)) (T i).2).E ∧
          (exceptionalDivisor (T i).2).support =
            ⋃ H ∈ (geoTransformAlong (windowRecord (w i)) (T i).2).E, H ∧
          (exceptionalDivisor (T i).2).support = (T i).2.proj ⁻¹' (w i).carrier ∧
          IsIsomorphismOver N (T i).2.proj (w i).carrierᶜ) ∧
        TowersCompatible T := by
  obtain ⟨N, ι, hι, w, hcov, hthin, m, T, hlen, hcan, hres, -, hcomp⟩ :=
    exists_embeddingIndependent_principalization X
  exact ⟨N, ι, hι, w, hcov, hthin, m, T, hlen, hcan, hres, fun i =>
    principalization_of_isGeoResolution (w i) (isInvDomain_windowRecord (k := N) le_rfl (w i) (hthin i))
      (T i).2 (hres i), hcomp⟩

end Compact

end

end Hironaka.Analytic.Unibranch.HironakaG11VanishingPrincipalization
