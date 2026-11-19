import Hironaka.Analytic.Unibranch.HironakaG11CompatibleCanonicalTowers

/-!
# The first canonical glued step for window records with transport (goal G11, route step 1)

For window records `𝔪 i` with transport along admissible overlaps (`RecordsTransport`, the input of
`HironakaG11CompatibleCanonicalTowers`), the FIRST canonical centres (the level sets of the common
maximum `λ` of the first-stage values) are compatible local smooth centres of `X`; their glued centre
is closed (it lies over the compact footprints), analytic, contained in the images of the
cosupports, nonempty when some cosupport is nonempty, and, when the cosupports lie over the singular
locus (the Hilbert–Samuel records: the cosupports are the traces of the maximal stratum), it is the
centre of a singular-centre blowup of `X`.

* `recordLevelCentres`, `recordLevelCentres_compatible`: the `λ`-level centres for any common bound
  `λ` (generic form of `HironakaG11VanishingWindows.levelSetCentres`);
* **`exists_canonical_first_glued_step`**.

No named proposition; nothing proves or assumes G11.
Blueprint: `hironaka-g11-resume-canonical-first-step.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG11CanonicalFirstStep

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences
  Hironaka HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11CompatibleAnalyticCover
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace SmoothCentreModification
  HironakaG11SingularCentreModification
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq
  MarkedIdealBiholomorphism
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open _root_.Hironaka.BlowupTowerIsomorphism (IsTowerIso)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ] {ι : Type*}
  (R : ResolutionInvariant.{0} N k Λ) {w : ι → DimEmbedding X N} (𝔪 : ∀ i, MarkedIdeal N (Amb w i))

/-- The first-stage value of the `i`-th record. -/
abbrev firstValue (i : ι) (y : (w i).ambient) : Λ :=
  R.inv (𝔪 i) (BlowupTower.refl : BlowupTower (Amb w i) (Amb w i)) y

variable {R 𝔪} (hD : ∀ i, IsInvDomain k (𝔪 i)) (hcos : ∀ i, (𝔪 i).cosupp ⊆ (w i).carrier)

/-- **The `λ`-level centres of the records** for a common bound `λ` of the first-stage values on the
cosupports: closed submanifolds of the windows by the admissibility of the route invariant. -/
def recordLevelCentres (lam : Λ) (hlam : ∀ i, ∀ y ∈ (𝔪 i).cosupp, firstValue R 𝔪 i y ≤ lam) :
    LocalSmoothCentres X ι where
  emb i := (w i).toLocalEmbedding
  window _ := ⊤
  centre i := (Subtype.val : (⊤ : Opens (w i).ambient) → (w i).ambient) ⁻¹'
    {y | y ∈ (𝔪 i).cosupp ∧ firstValue R 𝔪 i y = lam}
  isClosedSubmanifold i :=
    (R.isInvValue.admissible (𝔪 i) (hD i) BlowupTower.refl trivial ⊤ lam
      (fun y hy _ => hlam i y hy)).1
  centre_subset i := fun _ hx => hcos i hx.1

variable {Adm : ∀ (i j : ι) (U : Opens (w i).ambient) (U' : Opens (w j).ambient),
  (CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U) → Prop}
  (hAdm : ∀ i j (c : (w i).carrier) (c' : (w j).carrier),
    (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c →
    ∃ (U : Opens (w i).ambient) (U' : Opens (w j).ambient)
      (Φ : CMfd.of (n := N) U' ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ CMfd.of (n := N) U)
      (hc' : c'.val ∈ U') (hc : c.val ∈ U), Φ ⟨c'.val, hc'⟩ = ⟨c.val, hc⟩ ∧ Adm i j U U' Φ)
  (hTr : RecordsTransport R 𝔪 Adm)

include hAdm hTr in
/-- **First-stage transport at points with the same image**: if `c` lies in the cosupport of `𝔪 i`
and `c'` of window `j` has the same image in `X`, then `c'` lies in the cosupport of `𝔪 j` with the
same first-stage value. -/
theorem first_transport (i j : ι) (c : (w i).carrier) (c' : (w j).carrier)
    (h : (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
    (hc : c.val ∈ (𝔪 i).cosupp) :
    c'.val ∈ (𝔪 j).cosupp ∧ firstValue R 𝔪 j c'.val = firstValue R 𝔪 i c.val := by
  obtain ⟨U, U', Φ, hc'U', hcU, hΦ, hadm⟩ := hAdm i j c c' h
  have h0 := hTr i j U U' Φ hadm (BlowupTower.refl : BlowupTower (Amb w i) (Amb w i))
    (BlowupTower.refl : BlowupTower (Amb w j) (Amb w j)) trivial trivial Φ IsTowerIso.refl
    ⟨c'.val, hc'U'⟩
  have hΦv : ((Φ ⟨c'.val, hc'U'⟩ : U) : (w i).ambient) = c.val := congrArg Subtype.val hΦ
  have hin : ((Φ ⟨c'.val, hc'U'⟩ : U) : (w i).ambient) ∈ (geoTransformAlong (𝔪 i)
      (BlowupTower.refl : BlowupTower (Amb w i) (Amb w i))).cosupp := by
    rw [hΦv]
    exact hc
  refine ⟨h0.1.mp hin, ?_⟩
  have h1 := h0.2 hin
  change R.inv (𝔪 j) BlowupTower.refl c'.val = R.inv (𝔪 i) BlowupTower.refl c.val
  rw [h1]
  exact congrArg (R.inv (𝔪 i) (BlowupTower.refl : BlowupTower (Amb w i) (Amb w i))) hΦv

include hAdm hTr in
/-- **The level centres are compatible.** -/
theorem recordLevelCentres_compatible (lam : Λ)
    (hlam : ∀ i, ∀ y ∈ (𝔪 i).cosupp, firstValue R 𝔪 i y ≤ lam) :
    (recordLevelCentres hD hcos lam hlam).Compatible := by
  apply (recordLevelCentres hD hcos lam hlam).compatible_of_levelSet_overlap
    (fun i => {x | x.val ∈ (𝔪 i).cosupp}) (fun i x => firstValue R 𝔪 i x.val) lam (fun i => rfl)
  intro i j y z hyz hy
  exact first_transport hAdm hTr i j ⟨y.val.val, y.property⟩ ⟨z.val.val, z.property⟩ hyz.symm hy

variable {K : ∀ i, Set (w i).ambient}
  (hcover : ∀ i (c : (w i).carrier), c.val ∈ (𝔪 i).cosupp → ∃ j, ∃ c' : (w j).carrier,
    c'.val ∈ K j ∧ (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)

include hD hcos hAdm hTr hcover in
/-- **The first canonical glued step.** For finitely many windows of one ambient dimension with
records which transport along admissible overlaps, compact footprints covering the images of the
cosupports, and cosupports over the singular locus: with `λ` the common maximum of the first-stage
values, the `λ`-level centres are compatible, their glued centre is closed, analytic, contained in
the images of the cosupports, nonempty when some cosupport is nonempty, and the centre of a
singular-centre blowup of `X`. -/
theorem exists_canonical_first_glued_step [Finite ι] (hK : ∀ i, IsCompact (K i))
    (hsing : ∀ i (c : (w i).carrier), c.val ∈ (𝔪 i).cosupp →
      (w i).toLocalEmbedding.toPoint c ∈ intrinsicSingularLocus X.obj)
    (hne : ∃ i, ((𝔪 i).cosupp).Nonempty) :
    ∃ (lam : Λ) (hlam : ∀ i, ∀ y ∈ (𝔪 i).cosupp, firstValue R 𝔪 i y ≤ lam),
      (recordLevelCentres hD hcos lam hlam).Compatible ∧
      IsClosed (recordLevelCentres hD hcos lam hlam).support ∧
      (recordLevelCentres hD hcos lam hlam).support.Nonempty ∧
      (recordLevelCentres hD hcos lam hlam).support ⊆
        {x | ∃ i, ∃ c : (w i).carrier, c.val ∈ (𝔪 i).cosupp ∧ (w i).toLocalEmbedding.toPoint c = x} ∧
      ∃ (hS : X.IsAnalyticSubset (recordLevelCentres hD hcos lam hlam).support)
        (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
        IsSmoothCentreBlowup p
          (OriginalAnalyticClosedSubspace.inclusion X (recordLevelCentres hD hcos lam hlam).support hS) ∧
        IsSingularCentreStep p ∧ IsSingularCentreModification p ∧
        Function.Surjective p.hom.left.base ∧
        IsIsoOver p (recordLevelCentres hD hcos lam hlam).supportᶜ := by
  -- the common maximum over the footprints
  obtain ⟨i₀, y₀, hy₀⟩ := hne
  obtain ⟨j₀, c₀, hc₀K, hc₀⟩ := hcover i₀ ⟨y₀, hcos i₀ hy₀⟩ hy₀
  have hc₀c := (first_transport hAdm hTr i₀ j₀ ⟨y₀, hcos i₀ hy₀⟩ c₀ hc₀ hy₀).1
  have hpiece : ∀ i, ((𝔪 i).cosupp ∩ K i).Nonempty →
      ∃ y ∈ (𝔪 i).cosupp ∩ K i, ∀ y' ∈ (𝔪 i).cosupp ∩ K i, firstValue R 𝔪 i y' ≤ firstValue R 𝔪 i y := by
    intro i hnei
    have hSc : IsClosed (𝔪 i).cosupp :=
      GiraudAlong.isClosed_cosupport_along (hD i).isWellFormed.isCoherent
        (hD i).isWellFormed.isClosedSubmanifold_N _
    exact ((R.isInvValue.usc _ (hD i) BlowupTower.refl trivial).mono inter_subset_left).exists_isMaxOn
      ((hK i).inter_left hSc) hnei
  choose f hf hfmax using hpiece
  have : Finite {i // ((𝔪 i).cosupp ∩ K i).Nonempty} := Subtype.finite
  obtain ⟨i₁, -, hi₁⟩ := Set.exists_max_image (univ : Set {i // ((𝔪 i).cosupp ∩ K i).Nonempty})
    (fun i => firstValue R 𝔪 i.1 (f i.1 i.2)) (Set.toFinite _) ⟨⟨j₀, c₀.val, hc₀c, hc₀K⟩, trivial⟩
  set lam := firstValue R 𝔪 i₁.1 (f i₁.1 i₁.2) with hlamdef
  -- every value is bounded by the footprint maximum
  have hlam : ∀ i, ∀ y ∈ (𝔪 i).cosupp, firstValue R 𝔪 i y ≤ lam := by
    intro i y hy
    obtain ⟨j, c', hc'K, hc'⟩ := hcover i ⟨y, hcos i hy⟩ hy
    obtain ⟨hc'c, hv⟩ := first_transport hAdm hTr i j ⟨y, hcos i hy⟩ c' hc' hy
    have := (hfmax j ⟨c'.val, hc'c, hc'K⟩ c'.val ⟨hc'c, hc'K⟩).trans (hi₁ ⟨j, c'.val, hc'c, hc'K⟩ trivial)
    rw [← hv]
    exact this
  set F := recordLevelCentres hD hcos lam hlam with hFdef
  have hc := recordLevelCentres_compatible hD hcos hAdm hTr lam hlam
  -- the glued centre lies over the footprints and over the cosupports
  have hsupp : ∀ x ∈ F.support, ∃ i, ∃ c : (w i).carrier, c.val ∈ (𝔪 i).cosupp ∧ c.val ∈ K i ∧
      firstValue R 𝔪 i c.val = lam ∧ (w i).toLocalEmbedding.toPoint c = x := by
    intro x hx
    obtain ⟨i, d, hd, rfl⟩ := F.mem_support.mp hx
    obtain ⟨hdc, hdv⟩ := hd
    obtain ⟨j, c', hc'K, hc'⟩ := hcover i ⟨d.val.val, d.property⟩ hdc
    obtain ⟨hc'c, hv⟩ := first_transport hAdm hTr i j ⟨d.val.val, d.property⟩ c' hc' hdc
    exact ⟨j, c', hc'c, hc'K, hv.trans hdv, hc'⟩
  have hcl : IsClosed F.support := by
    apply F.isClosed_support_of_finite hc (fun i => (w i).toLocalEmbedding.toPoint ''
      ((Subtype.val : (w i).carrier → (w i).ambient) ⁻¹' ((𝔪 i).cosupp ∩ K i)))
    · intro i
      have hSc : IsClosed (𝔪 i).cosupp :=
        GiraudAlong.isClosed_cosupport_along (hD i).isWellFormed.isCoherent
          (hD i).isWellFormed.isClosedSubmanifold_N _
      have hcpt : IsCompact ((Subtype.val : (w i).carrier → (w i).ambient) ⁻¹' ((𝔪 i).cosupp ∩ K i)) :=
        Topology.IsInducing.subtypeVal.isCompact_preimage' ((hK i).inter_left hSc)
          (fun y hy => ⟨⟨y, hcos i hy.1⟩, rfl⟩)
      exact hcpt.image (w i).toLocalEmbedding.isOpenEmbedding_toPoint.continuous
    · rintro i _ ⟨c, -, rfl⟩
      exact ⟨⟨⟨c.val, trivial⟩, c.property⟩, rfl⟩
    · intro x hx
      obtain ⟨i, c, hcc, hcK, -, rfl⟩ := hsupp x hx
      exact mem_iUnion.mpr ⟨i, c, ⟨hcc, hcK⟩, rfl⟩
  have hsub : F.support ⊆
      {x | ∃ i, ∃ c : (w i).carrier, c.val ∈ (𝔪 i).cosupp ∧ (w i).toLocalEmbedding.toPoint c = x} := by
    intro x hx
    obtain ⟨i, c, hcc, -, -, rfl⟩ := hsupp x hx
    exact ⟨i, c, hcc, rfl⟩
  have hsingF : F.support ⊆ intrinsicSingularLocus X.obj := by
    intro x hx
    obtain ⟨i, c, hcc, -, -, rfl⟩ := hsupp x hx
    exact hsing i c hcc
  have hnonempty : F.support.Nonempty := by
    have hmem : f i₁.1 i₁.2 ∈ (𝔪 i₁.1).cosupp ∩ K i₁.1 := hf i₁.1 i₁.2
    refine ⟨(w i₁.1).toLocalEmbedding.toPoint ⟨f i₁.1 i₁.2, hcos i₁.1 hmem.1⟩,
      F.mem_support.mpr ⟨i₁.1, ⟨⟨f i₁.1 i₁.2, trivial⟩, hcos i₁.1 hmem.1⟩, ⟨hmem.1, rfl⟩, rfl⟩⟩
  exact ⟨lam, hlam, hc, hcl, hnonempty, hsub, F.exists_singularCentreBlowup hc hcl hsingF⟩

end

end Hironaka.Analytic.Unibranch.HironakaG11CanonicalFirstStep
