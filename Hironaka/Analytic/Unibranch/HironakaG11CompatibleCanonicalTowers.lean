import Hironaka.Analytic.Unibranch.HironakaG11VanishingPrincipalization

/-!
# Simultaneous canonical towers of window records with transport (goal G11, route steps 1/2/5)

The construction of `HironakaG11VanishingPrincipalization` for ANY family of window records, so that
it applies to the Hilbert–Samuel records as soon as their values transport along overlaps (lane
G11B, human decision I-1296 C-0001): finitely many windows `w i` of one ambient dimension, records
`𝔪 i` on the ambient windows (in the domain of a route invariant `R` with well-ordered values) whose
cosupports lie in the carriers, a class `Adm` of admissible overlap biholomorphisms of the ambient
windows, and compact footprints `K i` covering the images of the cosupports.

* `RecordsTransport R 𝔪 Adm`: along isomorphic restrictions (over an admissible `Φ`) of canonical
  towers of two records, cosupports correspond and values agree (for the vanishing-ideal records this
  is G11B's `inv_vanishingRecord_eq_on_overlap`: `recordsTransport_vanishing`; for the
  Hilbert–Samuel records it is the open (3b-mark) step of lane G11B);
* `GStage m`: canonical towers of the records, of length `m`, compatible over every admissible
  overlap biholomorphism (`AdmCompatible`); `GStage.zero`, `GStage.next` (blow up the glued centres,
  the cosupport points whose value bounds all footprint values), `gstage`;
* **`exists_compatible_canonical_resolutions`**: with transport, admissible biholomorphisms at all
  pairs of carrier points with the same image (`hAdm`), and footprints covering the images of the
  cosupports, the glued canonical towers terminate: canonical towers of all records, of one length,
  resolutions of the records, compatible over every admissible biholomorphism;
* `adm_exists_vanishing`, `recordsTransport_vanishing`: the hypotheses hold for the vanishing-ideal
  records with `Adm` = carrier-preserving biholomorphisms (so the theorem is not vacuous).

No named proposition equivalent to G11 is introduced (`RecordsTransport` is the embedding-independence
input of the canonical algorithm, proved here for the vanishing records); nothing proves or assumes
G11. Blueprint: `hironaka-g11-resume-compatible-canonical-towers.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11CompatibleCanonicalTowers

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences
  Hironaka HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq
  MarkedIdealBiholomorphism
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.ResolutionDriver (maxLocus)
open _root_.Hironaka.HironakaG11InvTransport (vanishingRecord inv_vanishingRecord_eq_on_overlap)
open _root_.Hironaka.BlowupTowerIsomorphism (IsTowerIso)

noncomputable section

section Generic

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ] {ι : Type*}
  (R : ResolutionInvariant.{0} N k Λ) {w : ι → DimEmbedding X N} (𝔪 : ∀ i, MarkedIdeal N (Amb w i))

/-- The cosupport of the transform of the `i`-th record along its tower. -/
abbrev rcos (T : Towers w) (i : ι) : Set (T i).1 :=
  (geoTransformAlong (𝔪 i) (T i).2).cosupp

/-- The value of the route invariant on the `i`-th record along its tower. -/
abbrev rvalue (T : Towers w) (i : ι) : (T i).1 → Λ :=
  R.inv (𝔪 i) (T i).2

variable (Adm : ∀ (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient),
  (CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U) → Prop)

/-- **Compatibility over the admissible overlap biholomorphisms.** -/
def AdmCompatible (T : Towers w) : Prop :=
  ∀ (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
    (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U),
    Adm i j U U' Φ → ∃ χ, IsTowerIso Φ (restrict U' (T j).2) (restrict U (T i).2) χ

/-- **Transport of the records along admissible overlaps**: along isomorphic restrictions (over an
admissible biholomorphism `Φ : U' ≅ U`) of canonical towers of the records `𝔪 i` and `𝔪 j`, the
cosupports correspond and the values agree. -/
def RecordsTransport : Prop :=
  ∀ (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
    (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U),
    Adm i j U U' Φ → ∀ {Y Y' : CMfd.{0} N} (T : BlowupTower (Amb w i) Y)
      (T' : BlowupTower (Amb w j) Y'), IsCanonical (𝔪 i) (R.inv (𝔪 i)) T →
      IsCanonical (𝔪 j) (R.inv (𝔪 j)) T' →
      ∀ (χ : CMfd.of (n := N) (openPreimage T' U') ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯
        CMfd.of (n := N) (openPreimage T U)),
      IsTowerIso Φ (restrict U' T') (restrict U T) χ → ∀ p : openPreimage T' U',
        ((((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong (𝔪 i) T).cosupp ↔
          (p : Y') ∈ (geoTransformAlong (𝔪 j) T').cosupp) ∧
        (((χ p : openPreimage T U) : Y) ∈ (geoTransformAlong (𝔪 i) T).cosupp →
          R.inv (𝔪 j) T' p = R.inv (𝔪 i) T (χ p)))

/-- **A stage**: canonical towers of the records, of length `m`, compatible over every admissible
overlap biholomorphism. -/
structure GStage (m : ℕ) where
  /-- The towers. -/
  T : Towers w
  length : ∀ i, (T i).2.length = m
  canonical : ∀ i, IsCanonical (𝔪 i) (R.inv (𝔪 i)) (T i).2
  compatible : AdmCompatible Adm T

/-- Stage `0`: the empty towers. -/
def GStage.zero : GStage R 𝔪 Adm 0 where
  T i := ⟨Amb w i, .refl⟩
  length _ := rfl
  canonical _ := trivial
  compatible _ _ _ _ Φ _ := ⟨Φ, IsTowerIso.refl⟩

variable (K : ∀ i, Set (w i).ambient)

/-- The values at the points of the cosupports over the footprints. -/
def gfootValues (T : Towers w) : Set Λ :=
  ⋃ i, rvalue R 𝔪 T i '' (rcos 𝔪 T i ∩ (T i).2.proj ⁻¹' K i)

/-- The glued centre on the `i`-th window. -/
def gcentre (T : Towers w) (i : ι) : Set (T i).1 :=
  {y | y ∈ rcos 𝔪 T i ∧ rvalue R 𝔪 T i y ∈ upperBounds (gfootValues R 𝔪 K T)}

variable {R 𝔪 Adm K} (hD : ∀ i, IsInvDomain k (𝔪 i)) (hcos : ∀ i, (𝔪 i).cosupp ⊆ (w i).carrier)
  (hcover : ∀ i (c : (w i).carrier), c.val ∈ (𝔪 i).cosupp → ∃ j, ∃ c' : (w j).carrier,
    c'.val ∈ K j ∧ (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
  (hAdm : ∀ i j (c : (w i).carrier) (c' : (w j).carrier),
    (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c →
    ∃ (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
      (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U)
      (hc' : c'.val ∈ U') (hc : c.val ∈ U), Φ ⟨c'.val, hc'⟩ = ⟨c.val, hc⟩ ∧ Adm i j U U' Φ)
  (hTr : RecordsTransport R 𝔪 Adm)

include hD hcos hcover hAdm hTr in
/-- **Every value is a footprint value.** -/
theorem rvalue_mem_gfootValues {m : ℕ} (s : GStage R 𝔪 Adm m) (i : ι) (y : (s.T i).1)
    (hy : y ∈ rcos 𝔪 s.T i) : rvalue R 𝔪 s.T i y ∈ gfootValues R 𝔪 K s.T := by
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i)
  have hx : (s.T i).2.proj y ∈ (𝔪 i).cosupp :=
    StepOneLowerDomain.proj_mem_cosupp_of_mem_cosupp
      (hD i).isWellFormed.isClosedSubmanifold_N (hD i).isWellFormed.isCoherent _ hTt hy
  obtain ⟨j, c', hc'K, hc'⟩ := hcover i ⟨_, hcos i hx⟩ hx
  obtain ⟨U, U', Ψ, hc'U', hxU, hΨc, hadm⟩ := hAdm i j ⟨_, hcos i hx⟩ c' hc'
  obtain ⟨χ, hiso⟩ := s.compatible i j U U' Ψ hadm
  let q : openPreimage (s.T i).2 U := ⟨y, hxU⟩
  have hχp : χ (χ.symm q) = q := χ.apply_symm_apply q
  have hp : ((χ (χ.symm q) : openPreimage (s.T i).2 U) : (s.T i).1) ∈ rcos 𝔪 s.T i := by
    rw [hχp]
    exact hy
  obtain ⟨hiff, hval⟩ := hTr i j U U' Ψ hadm (s.T i).2 (s.T j).2 (s.canonical i) (s.canonical j) χ hiso
    (χ.symm q)
  have hpc := hiff.mp hp
  have hpv := hval hp
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
  · change R.inv (𝔪 j) (s.T j).2 (χ.symm q).val = R.inv (𝔪 i) (s.T i).2 y
    rw [hpv, hχp]

include hD in
/-- **The footprint values have a greatest element.** -/
theorem exists_isGreatest_gfootValues [Finite ι] (hK : ∀ i, IsCompact (K i)) {m : ℕ}
    (s : GStage R 𝔪 Adm m) (hne : (gfootValues R 𝔪 K s.T).Nonempty) :
    ∃ M, IsGreatest (gfootValues R 𝔪 K s.T) M := by
  have hpiece : ∀ i, (rcos 𝔪 s.T i ∩ (s.T i).2.proj ⁻¹' K i).Nonempty →
      ∃ y ∈ rcos 𝔪 s.T i ∩ (s.T i).2.proj ⁻¹' K i,
        ∀ y' ∈ rcos 𝔪 s.T i ∩ (s.T i).2.proj ⁻¹' K i, rvalue R 𝔪 s.T i y' ≤ rvalue R 𝔪 s.T i y := by
    intro i hnei
    have hTt := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i)
    have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong (hD i) _ hTt
    have hSc : IsClosed (rcos 𝔪 s.T i) :=
      GiraudAlong.isClosed_cosupport_along hdomT.isWellFormed.isCoherent
        hdomT.isWellFormed.isClosedSubmanifold_N _
    have hSK : IsCompact (rcos 𝔪 s.T i ∩ (s.T i).2.proj ⁻¹' K i) :=
      ((HironakaLocalPrincipalization.isProperMap_proj (s.T i).2).isCompact_preimage (hK i)).inter_left hSc
    exact ((R.isInvValue.usc _ (hD i) _ (s.canonical i)).mono inter_subset_left).exists_isMaxOn hSK hnei
  choose f hf hfmax using hpiece
  obtain ⟨v, hv⟩ := hne
  obtain ⟨i, y, hy, -⟩ := mem_iUnion.mp hv
  have : Finite {i // (rcos 𝔪 s.T i ∩ (s.T i).2.proj ⁻¹' K i).Nonempty} := Subtype.finite
  obtain ⟨i₀, -, hi₀⟩ := Set.exists_max_image
    (univ : Set {i // (rcos 𝔪 s.T i ∩ (s.T i).2.proj ⁻¹' K i).Nonempty})
    (fun i => rvalue R 𝔪 s.T i.1 (f i.1 i.2)) (Set.toFinite _) ⟨⟨i, y, hy⟩, trivial⟩
  refine ⟨rvalue R 𝔪 s.T i₀.1 (f i₀.1 i₀.2), mem_iUnion.mpr ⟨i₀.1, _, hf _ _, rfl⟩, ?_⟩
  rintro v' hv'
  obtain ⟨i', y', hy', rfl⟩ := mem_iUnion.mp hv'
  exact (hfmax i' ⟨y', hy'⟩ y' hy').trans (hi₀ ⟨i', y', hy'⟩ trivial)

include hD hcos hcover hAdm hTr in
/-- The glued centre is empty or the maximum locus. -/
theorem gcentre_eq_empty_or_maxLocus {m : ℕ} (s : GStage R 𝔪 Adm m) (i : ι) :
    gcentre R 𝔪 K s.T i = ∅ ∨ gcentre R 𝔪 K s.T i = maxLocus (rvalue R 𝔪 s.T i) (rcos 𝔪 s.T i) := by
  rcases (gcentre R 𝔪 K s.T i).eq_empty_or_nonempty with h | ⟨y₀, hy₀c, hy₀⟩
  · exact Or.inl h
  · right
    ext y
    constructor
    · rintro ⟨hyc, hy⟩
      exact ⟨hyc, fun y' hy' => hy (rvalue_mem_gfootValues hD hcos hcover hAdm hTr s i y' hy')⟩
    · rintro ⟨hyc, hy⟩
      exact ⟨hyc, fun v hv => (hy₀ hv).trans (hy y₀ hy₀c)⟩

include hD hcos hcover hAdm hTr in
/-- The glued centre can be blown up. -/
theorem exists_blowup_gcentre {m : ℕ} (s : GStage R 𝔪 Adm m) (i : ι) :
    ∃ (Z : CMfd.{0} N) (π : Z → (s.T i).1), IsBlowupAlong N (gcentre R 𝔪 K s.T i) π := by
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i)
  rcases gcentre_eq_empty_or_maxLocus hD hcos hcover hAdm hTr s i with h | h
  · rw [h]
    exact ResolutionDriver.exists_blowup ∅
      (isAdmissibleCentre_empty (geoTransformAlong (𝔪 i) (s.T i).2)).1 interior_empty
  · rw [h]
    exact ResolutionDriver.exists_blowup _
      (R.isInvValue.isAdmissibleCentre_maxLocus (hD i) _ (s.canonical i) hTt).1
      (ResolutionInvariantDriver.interior_maxLocus_eq_empty (hD i) _ hTt _)

include hTr in
/-- The glued centres correspond on admissible overlaps. -/
theorem gcentre_preimage {m : ℕ} (s : GStage R 𝔪 Adm m) (i j : ι) (U : Opens (w i).ambient)
    (U' : Opens (w j).ambient)
    (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U)
    (hadm : Adm i j U U' Φ)
    {χ : CMfd.of (n := N) (openPreimage (s.T j).2 U') ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯
      CMfd.of (n := N) (openPreimage (s.T i).2 U)}
    (hiso : IsTowerIso Φ (restrict U' (s.T j).2) (restrict U (s.T i).2) χ) :
    χ ⁻¹' ((Subtype.val : openPreimage (s.T i).2 U → (s.T i).1) ⁻¹' gcentre R 𝔪 K s.T i) =
      (Subtype.val : openPreimage (s.T j).2 U' → (s.T j).1) ⁻¹' gcentre R 𝔪 K s.T j := by
  ext p
  obtain ⟨hiff, hval⟩ := hTr i j U U' Φ hadm (s.T i).2 (s.T j).2 (s.canonical i) (s.canonical j) χ hiso p
  simp only [mem_preimage, gcentre, mem_ofPred_eq]
  constructor
  · rintro ⟨hc, hv⟩
    refine ⟨hiff.mp hc, ?_⟩
    change R.inv (𝔪 j) (s.T j).2 p.val ∈ _
    rw [hval hc]
    exact hv
  · rintro ⟨hc, hv⟩
    have hc' := hiff.mpr hc
    refine ⟨hc', ?_⟩
    change R.inv (𝔪 i) (s.T i).2 (χ p).val ∈ _
    rw [← hval hc']
    exact hv

/-- The space of the blowup of the glued centre over the `i`-th window. -/
def gnextSpace {m : ℕ} (s : GStage R 𝔪 Adm m) (i : ι) : CMfd.{0} N :=
  (exists_blowup_gcentre hD hcos hcover hAdm hTr s i).choose

/-- The blowup of the glued centre over the `i`-th window. -/
def gnextMap {m : ℕ} (s : GStage R 𝔪 Adm m) (i : ι) :
    gnextSpace hD hcos hcover hAdm hTr s i → (s.T i).1 :=
  (exists_blowup_gcentre hD hcos hcover hAdm hTr s i).choose_spec.choose

theorem gnextMap_isBlowup {m : ℕ} (s : GStage R 𝔪 Adm m) (i : ι) :
    IsBlowupAlong N (gcentre R 𝔪 K s.T i) (gnextMap hD hcos hcover hAdm hTr s i) :=
  (exists_blowup_gcentre hD hcos hcover hAdm hTr s i).choose_spec.choose_spec

/-- **The next stage**: blow up the glued centres. -/
def GStage.next {m : ℕ} (s : GStage R 𝔪 Adm m) : GStage R 𝔪 Adm (m + 1) where
  T i := ⟨gnextSpace hD hcos hcover hAdm hTr s i,
    .step (s.T i).2 (gcentre R 𝔪 K s.T i) (gnextMap hD hcos hcover hAdm hTr s i)
      (gnextMap_isBlowup hD hcos hcover hAdm hTr s i)⟩
  length i := by
    show (s.T i).2.length + 1 = m + 1
    rw [s.length i]
  canonical i := ⟨s.canonical i, gcentre_eq_empty_or_maxLocus hD hcos hcover hAdm hTr s i⟩
  compatible := by
    intro i j U U' Φ hadm
    obtain ⟨χ, hiso⟩ := s.compatible i j U U' Φ hadm
    exact exists_isTowerIso_step hiso _ _ (gcentre_preimage hTr s i j U U' Φ hadm hiso)

include hD hcos hcover hAdm hTr in
/-- The values drop below the common maximum after the blowup of the glued centres. -/
theorem rvalue_next_lt {m : ℕ} (s : GStage R 𝔪 Adm m) {M : Λ}
    (hM : IsGreatest (gfootValues R 𝔪 K s.T) M) (i : ι)
    (z : ((s.next hD hcos hcover hAdm hTr).T i).1)
    (hz : z ∈ rcos 𝔪 (s.next hD hcos hcover hAdm hTr).T i) :
    rvalue R 𝔪 (s.next hD hcos hcover hAdm hTr).T i z < M := by
  have hπ := gnextMap_isBlowup hD hcos hcover hAdm hTr s i
  have hTt' := R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _
    ((s.next hD hcos hcover hAdm hTr).canonical i)
  have hπz : gnextMap hD hcos hcover hAdm hTr s i z ∈ rcos 𝔪 s.T i :=
    StepOneWellFounded.proj_mem_cosupp_step (hD i).isWellFormed.isClosedSubmanifold_N
      (hD i).isWellFormed.isCoherent (s.T i).2 _ _ hπ hTt' hz
  have hle : rvalue R 𝔪 s.T i (gnextMap hD hcos hcover hAdm hTr s i z) ≤ M :=
    hM.2 (rvalue_mem_gfootValues hD hcos hcover hAdm hTr s i _ hπz)
  have hnotC : gnextMap hD hcos hcover hAdm hTr s i z ∉ gcentre R 𝔪 K s.T i →
      rvalue R 𝔪 s.T i (gnextMap hD hcos hcover hAdm hTr s i z) < M := fun hC =>
    lt_of_le_of_ne hle fun h => hC ⟨hπz, by rw [h]; exact hM.2⟩
  change R.inv (𝔪 i) (.step (s.T i).2 (gcentre R 𝔪 K s.T i) (gnextMap hD hcos hcover hAdm hTr s i) hπ) z < M
  by_cases hzC : gnextMap hD hcos hcover hAdm hTr s i z ∈ gcentre R 𝔪 K s.T i
  · have hCne : (gcentre R 𝔪 K s.T i).Nonempty := ⟨_, hzC⟩
    have hCmax := (gcentre_eq_empty_or_maxLocus hD hcos hcover hAdm hTr s i).resolve_left hCne.ne_empty
    exact ((R.isInvValue.decrease _ (hD i) (s.T i).2 _ _ hπ (s.canonical i) hCne hCmax z hz).1
      hzC).trans_le hle
  · have heq : R.inv (𝔪 i) (.step (s.T i).2 (gcentre R 𝔪 K s.T i)
        (gnextMap hD hcos hcover hAdm hTr s i) hπ) z =
        rvalue R 𝔪 s.T i (gnextMap hD hcos hcover hAdm hTr s i z) := by
      by_cases hCne : (gcentre R 𝔪 K s.T i).Nonempty
      · have hCmax :=
          (gcentre_eq_empty_or_maxLocus hD hcos hcover hAdm hTr s i).resolve_left hCne.ne_empty
        exact (R.isInvValue.decrease _ (hD i) (s.T i).2 _ _ hπ (s.canonical i) hCne hCmax z hz).2 hzC
      · exact R.isInvValue.emptyStep _ (hD i) (s.T i).2 _ _ hπ (not_nonempty_iff_eq_empty.mp hCne)
          (s.canonical i) z hz
    rw [heq]
    exact hnotC hzC

variable (R 𝔪 Adm K) in
/-- **The stages of the glued canonical towers.** -/
def gstage : (m : ℕ) → GStage R 𝔪 Adm m
  | 0 => GStage.zero R 𝔪 Adm
  | m + 1 => (gstage m).next hD hcos hcover hAdm hTr

include hD hcos hcover hAdm hTr in
/-- **Termination**: at some stage every cosupport is empty. -/
theorem exists_gstage_cosupp_eq_empty [Finite ι] [WellFoundedLT Λ] (hK : ∀ i, IsCompact (K i)) :
    ∃ m, ∀ i, rcos 𝔪 (gstage R 𝔪 Adm K hD hcos hcover hAdm hTr m).T i = ∅ := by
  by_contra hcon
  push Not at hcon
  have hne : ∀ m, (gfootValues R 𝔪 K (gstage R 𝔪 Adm K hD hcos hcover hAdm hTr m).T).Nonempty :=
    fun m => by
      obtain ⟨i, y, hy⟩ := hcon m
      exact ⟨_, rvalue_mem_gfootValues hD hcos hcover hAdm hTr _ i y hy⟩
  choose M hM using fun m => exists_isGreatest_gfootValues hD hK
    (gstage R 𝔪 Adm K hD hcos hcover hAdm hTr m) (hne m)
  have hlt : ∀ m, M (m + 1) < M m := by
    intro m
    obtain ⟨i, z, hz, hzM⟩ := mem_iUnion.mp (hM (m + 1)).1
    rw [← hzM]
    exact rvalue_next_lt hD hcos hcover hAdm hTr (gstage R 𝔪 Adm K hD hcos hcover hAdm hTr m) (hM m) i z
      hz.1
  obtain ⟨m, hm⟩ := WellFounded.not_rel_apply_succ (r := (· < ·)) M
  exact hm (hlt m)

include hD hcos hcover hAdm hTr in
/-- **Compatible canonical resolutions of window records with transport.** For finitely many windows
of one ambient dimension, records in the domain of a route invariant with well-ordered values whose
cosupports lie in the carriers and transport along the admissible overlap biholomorphisms (which
exist at every pair of carrier points with the same image), and compact footprints covering the
images of the cosupports, there are canonical towers of all records, of one length, which resolve
the records and are isomorphic over every admissible overlap biholomorphism. -/
theorem exists_compatible_canonical_resolutions [Finite ι] [WellFoundedLT Λ]
    (hK : ∀ i, IsCompact (K i)) :
    ∃ (m : ℕ) (T : Towers w),
      (∀ i, (T i).2.length = m) ∧
      (∀ i, IsCanonical (𝔪 i) (R.inv (𝔪 i)) (T i).2) ∧
      (∀ i, IsGeoResolution (𝔪 i) (T i).2) ∧
      AdmCompatible Adm T := by
  obtain ⟨m, hm⟩ := exists_gstage_cosupp_eq_empty hD hcos hcover hAdm hTr hK
  set s := gstage R 𝔪 Adm K hD hcos hcover hAdm hTr m
  exact ⟨m, s.T, s.length, s.canonical,
    fun i => ⟨R.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ (s.canonical i), hm i⟩, s.compatible⟩

end Generic

/-! ### The vanishing-ideal records satisfy the hypotheses -/

section Vanishing

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ] {ι : Type*}
  (R : ResolutionInvariant.{0} N k Λ) (w : ι → DimEmbedding X N)

/-- The carrier-preserving overlap biholomorphisms. -/
def carrierAdm (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
    (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U) :
    Prop :=
  ∀ p : U', ((Φ p : U) : (w i).ambient) ∈ (w i).carrier ↔ (p : (w j).ambient) ∈ (w j).carrier

/-- Carrier-preserving overlap biholomorphisms exist at all pairs of carrier points with the same
image (G11B's ambient biholomorphism). -/
theorem adm_exists_vanishing (i j : ι) (c : (w i).carrier) (c' : (w j).carrier)
    (h : (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c) :
    ∃ (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
      (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U)
      (hc' : c'.val ∈ U') (hc : c.val ∈ U), Φ ⟨c'.val, hc'⟩ = ⟨c.val, hc⟩ ∧ carrierAdm w i j U U' Φ :=
  exists_overlap_diffeo (w i) (w j) c c' h.symm

variable {w} in
/-- **The vanishing-ideal records transport along carrier-preserving overlaps** (G11B's
`inv_vanishingRecord_eq_on_overlap` and the correspondence of cosupports). -/
theorem recordsTransport_vanishing (hD : ∀ i, IsInvDomain k (windowRecord (w i))) :
    RecordsTransport R (fun i => windowRecord (w i)) (carrierAdm w) := by
  intro i j U U' Φ hadm Y Y' T T' hcan hcan' χ hiso p
  have hset := valueSet_preimage_on_overlap R (hD i) (hD j) U U' Φ hadm hcan' hcan hiso univ
  have hp := congrArg (fun S => p ∈ S) hset
  simp only [mem_preimage, mem_ofPred_eq, mem_univ, and_true, eq_iff_iff] at hp
  exact ⟨hp, fun hc =>
    (inv_vanishingRecord_eq_on_overlap R (hD i) (hD j) U U' Φ hadm hcan' hcan hiso p hc).2⟩

end Vanishing

end

end Hironaka.Analytic.Unibranch.HironakaG11CompatibleCanonicalTowers
