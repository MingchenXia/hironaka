import Hironaka.Invariant.CanonicalCentres
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Invariant.NonmonomialOrderMonomialTransport
import Hironaka.Invariant.ResolutionInvariantSegments

/-!
# Local equivariance of canonical towers (first brick of EQ_d)

Lane G34 (run 0080, round 8).  Blueprint: `hironaka-g34-resume-canonical-local-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §2(c)(i), §5.

Let `T` be a tower over `X` each of whose centres is empty or the maximum locus, on the cosupport, of an invariant of a
marked ideal `𝔪` (`IsCanonical`), and let `φ : V ≅ V'` be a biholomorphism between two opens of `X` carrying `𝔪|_{V'}` to
`𝔪|_V`.  Then the restrictions `T|_V` and `T|_{V'}` are isomorphic over `φ` (`IsTowerIso`), stage by stage, INCLUDING the
empty steps: no "up to empty steps" is needed.  Indeed the restricted centres are the traces of the GLOBAL centres, and by
the locality (5) and the naturality (6) of the invariant the value at `p` over `V` is the GLOBAL value at `p`, which is the
GLOBAL value at the corresponding point over `V'`; so `p` lies in the global maximum locus iff its image does.  This is
the local (open-to-open) form of `CanonicalResolution.exists_isTowerIso_of_isGeoResolution` for ONE tower.

## Main results

* `exists_isTowerIso_step`: an isomorphism of towers extends over blowups along corresponding centres;
* `mem_maxLocus_iff_of`: maximum-locus membership is decided by cosupport membership and the value;
* **`exists_isTowerIso_restrict_of_isCanonical_of_forall`** (generic): if, along every canonical prefix (with an extra
  prefix-closed property `P`), every isomorphism of the restrictions over `φ` maps the trace of the maximum locus over `V`
  onto the trace over `V'`, then every canonical tower restricts to isomorphic towers over `φ`;
* **`exists_isTowerIso_restrict_of_isCanonical`**: the case of a resolution invariant (`ResolutionInvariantSeq`, e.g.
  `CanonicalCentres.invFamily`), from properties (5) and (6);
* **`exists_isTowerIso_restrict_of_towerInvAlong`**: the case of the monomial invariant `towerInvAlong` along multiple test
  blow-ups (no domain hypothesis: its locality and naturality are unconditional);
* `pullback_restrict_geoTransformAlong`: transforms of a `φ`-natural marked ideal along a tower with isomorphic restrictions
  are natural for the lifted biholomorphism;
* **`exists_isTowerIso_restrict_append`**: equivariance of a concatenation from that of the head over `φ` and that of the
  tail over the lifted biholomorphism;
* **`exists_isTowerIso_restrict_append_of_isCanonical`**, `..._of_towerInvAlong`: appending a canonical block of a marked
  ideal of the current stage which is natural for the lifted biholomorphism keeps the tower equivariant (the concatenation
  step of the re-derivation of J4 / K3 with an equivariance conclusion).

New file; no existing statement changed; no named input.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG34CanonicalLocalEquivariance

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### Two elementary facts -/

section Elementary

/-- **An isomorphism of towers extends over blowups along corresponding centres**: if `χ⁻¹ C = C'`, the blowups `π'` along
`C'` and `π` along `C` are isomorphic over `χ` (`BlowupUniqueness.exists_biholomorphism_over`). -/
theorem exists_isTowerIso_step {X X' : CMfd.{u} n} {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {Y' Y Z' Z : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (h : IsTowerIso Φ T' T χ)
    {C' : Set Y'} {π' : Z' → Y'} (hπ' : IsBlowupAlong n C' π') {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hC : χ ⁻¹' C = C') :
    ∃ χ₁ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z,
      IsTowerIso Φ (.step T' C' π' hπ') (.step T C π hπ) χ₁ := by
  have hB := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply
    χ.symm_apply_apply hπ
  rw [hC] at hB
  obtain ⟨e, f, he, hf, hπe, -, hfe, hef⟩ := BlowupUniqueness.exists_biholomorphism_over hπ' hB
  refine ⟨⟨⟨e, f, congrFun hfe, congrFun hef⟩, he, hf⟩, IsTowerIso.step h hπ' hπ _ (fun p => ?_) hC⟩
  have h1 : χ.symm (π (e p)) = π' p := congrFun hπe p
  show π (e p) = χ (π' p)
  rw [← h1, χ.apply_symm_apply]

/-- **Maximum-locus membership of two points** agrees when their cosupport membership agrees and, on the cosupport, their
values agree. -/
theorem mem_maxLocus_iff_of {Λ : Type v} [LinearOrder Λ] {Y : Type*} (f : Y → Λ) (s : Set Y) {a b : Y}
    (hs : a ∈ s ↔ b ∈ s) (hf : a ∈ s → f a = f b) : a ∈ maxLocus f s ↔ b ∈ maxLocus f s := by
  constructor
  · rintro ⟨ha, hmax⟩
    refine ⟨hs.mp ha, fun y hy => ?_⟩
    rw [← hf ha]
    exact hmax y hy
  · rintro ⟨hb, hmax⟩
    have ha := hs.mpr hb
    refine ⟨ha, fun y hy => ?_⟩
    rw [hf ha]
    exact hmax y hy

end Elementary

/-! ### The generic statement -/

section Generic

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] (𝔪 : MarkedIdeal n X)
  (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) {V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')

/-- **Local equivariance of a canonical tower, generic form.**  Let `P` be a property of towers inherited by prefixes, and
suppose that along every canonical tower `T` with `P`, every isomorphism `χ : T|_V ≅ T|_{V'}` over `φ` maps the trace over
`V` of the maximum locus of `inv T` on the cosupport onto its trace over `V'`.  Then every canonical tower with `P` has
isomorphic restrictions to `V` and `V'` over `φ` (empty steps included). -/
theorem exists_isTowerIso_restrict_of_isCanonical_of_forall
    (P : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop)
    (hP : ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      P (.step T C π hπ) → P T)
    (hsel : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 inv T → P T →
      ∀ χ : CMfd.of (n := n) (openPreimage T V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T V'),
      IsTowerIso φ (restrict V T) (restrict V' T) χ → ∀ p : openPreimage T V,
        ((p : Y) ∈ maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp ↔
          ((χ p : openPreimage T V') : Y) ∈ maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 inv T → P T →
      ∃ χ : CMfd.of (n := n) (openPreimage T V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T V'), IsTowerIso φ (restrict V T) (restrict V' T) χ
  | _, .refl, _, _ => ⟨φ, IsTowerIso.refl⟩
  | _, .step T C π hπ, hcan, hPT => by
      obtain ⟨hT, hC⟩ := hcan
      have hPT' := hP T C π hπ hPT
      obtain ⟨χ, hχ⟩ := exists_isTowerIso_restrict_of_isCanonical_of_forall P hP hsel T hT hPT'
      have hCC : χ ⁻¹' ((Subtype.val : openPreimage T V' → _) ⁻¹' C) =
          (Subtype.val : openPreimage T V → _) ⁻¹' C := by
        ext p
        rcases hC with rfl | rfl
        · simp
        · exact (hsel T hT hPT' χ hχ p).symm
      exact exists_isTowerIso_step hχ _ _ hCC

end Generic

/-! ### Resolution invariants -/

section Invariant

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}
  (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪)
  {V V' : Opens X} (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')

include hdom in
/-- **Local equivariance of a canonical tower of a resolution invariant** (properties (5) and (6)): if `φ : V ≅ V'` carries
`𝔪|_{V'}` to `𝔪|_V`, every tower `T` whose centres are empty or maximum loci of `R.inv 𝔪` has `T|_V ≅ T|_{V'}` over `φ`. -/
theorem exists_isTowerIso_restrict_of_isCanonical
    (hφ : MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) =
      MarkedIdeal.pullback (Subtype.val : V → X) 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsCanonical 𝔪 (R.inv 𝔪) T) :
    ∃ χ : CMfd.of (n := n) (openPreimage T V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T V'), IsTowerIso φ (restrict V T) (restrict V' T) χ := by
  refine exists_isTowerIso_restrict_of_isCanonical_of_forall 𝔪 (R.inv 𝔪) φ (fun _ => True)
    (fun _ _ _ _ _ => trivial) ?_ T hT trivial
  intro Y₀ T₀ hT₀ _ χ hχ p
  have hdV' := InvDomainTowerAlong.isInvDomain_pullback_val V' hdom
  have hTt := R.isInvValue.isGeoTestTower_of_isCanonical hdom T₀ hT₀
  have hcanV' := Seq.ResolutionInvariantExt.isCanonical_restrict R hdom V' T₀ hT₀
  have hTtV' := R.isInvValue.isGeoTestTower_of_isCanonical hdV' _ hcanV'
  have hcosV := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent V T₀ hTt
  have hcosV' := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent V' T₀ hTt
  have hcosφ := IsTowerIso.cosupp_geoTransformAlong φ hdV'.isWellFormed.isClosedSubmanifold_N
    hdV'.isWellFormed.isCoherent hχ hTtV'
  rw [hφ] at hcosφ
  have hs : (p : Y₀) ∈ (geoTransformAlong 𝔪 T₀).cosupp ↔
      ((χ p : openPreimage T₀ V') : Y₀) ∈ (geoTransformAlong 𝔪 T₀).cosupp := by
    have h1 : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) 𝔪) (restrict V T₀)).cosupp ↔
        (p : Y₀) ∈ (geoTransformAlong 𝔪 T₀).cosupp := by
      rw [hcosV]; rfl
    have h2 : χ p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) (restrict V' T₀)).cosupp ↔
        ((χ p : openPreimage T₀ V') : Y₀) ∈ (geoTransformAlong 𝔪 T₀).cosupp := by
      rw [hcosV']; rfl
    rw [← h1, ← h2, hcosφ]
    rfl
  refine mem_maxLocus_iff_of _ _ hs fun hp => ?_
  have hpV' : χ p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) (restrict V' T₀)).cosupp := by
    rw [hcosV']
    exact hs.mp hp
  have h5 := R.isInvValue.restrictOpen 𝔪 hdom V T₀ hT₀ p hp
  have h5' := R.isInvValue.restrictOpen 𝔪 hdom V' T₀ hT₀ (χ p) (hs.mp hp)
  have h6 := R.isInvValue.towerIso φ (MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) hdV' (restrict V T₀)
    (restrict V' T₀) χ hχ hcanV' p hpV'
  rw [hφ] at h6
  rw [← h5, h6, h5']

end Invariant

/-! ### The monomial invariant `towerInvAlong` -/

section Monomial

variable {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
  {V V' : Opens X} (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')

include hN h𝔞 in
/-- **Local equivariance of a canonical tower of the monomial invariant**: if `φ : V ≅ V'` carries `𝔪|_{V'}` to `𝔪|_V`,
every multiple test blow-up `T` of `𝔪` whose centres are empty or maximum loci of `towerInvAlong 𝔪` has
`T|_V ≅ T|_{V'}` over `φ` (`towerInvAlong_restrict`, `towerInvAlong_isTowerIso`). -/
theorem exists_isTowerIso_restrict_of_towerInvAlong
    (hφ : MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) =
      MarkedIdeal.pullback (Subtype.val : V → X) 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsCanonical 𝔪 (fun {Y} Q => MonomialStepAlong.towerInvAlong 𝔪 (Y := Y) Q) T)
    (hTt : IsGeoTestTower 𝔪 T) :
    ∃ χ : CMfd.of (n := n) (openPreimage T V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T V'), IsTowerIso φ (restrict V T) (restrict V' T) χ := by
  refine exists_isTowerIso_restrict_of_isCanonical_of_forall 𝔪
    (fun {Y} Q => MonomialStepAlong.towerInvAlong 𝔪 (Y := Y) Q) φ (fun T => IsGeoTestTower 𝔪 T)
    (fun _ _ _ _ h => h.1) ?_ T hT hTt
  intro Y₀ T₀ _ hTt₀ χ hχ p
  have hN' := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN V'
  have h𝔞' := GermIdealPullbackCalculus.isCoherent_pullback (contMDiff_subtype_val (U := V')) h𝔞
  have hTtV' := isGeoTestTower_restrict (U := V') hN h𝔞 T₀ hTt₀
  have hcosV := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hN h𝔞 V T₀ hTt₀
  have hcosV' := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hN h𝔞 V' T₀ hTt₀
  have hcosφ := IsTowerIso.cosupp_geoTransformAlong (𝔪 := MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) φ hN' h𝔞'
    hχ hTtV'
  rw [hφ] at hcosφ
  have hs : (p : Y₀) ∈ (geoTransformAlong 𝔪 T₀).cosupp ↔
      ((χ p : openPreimage T₀ V') : Y₀) ∈ (geoTransformAlong 𝔪 T₀).cosupp := by
    have h1 : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) 𝔪) (restrict V T₀)).cosupp ↔
        (p : Y₀) ∈ (geoTransformAlong 𝔪 T₀).cosupp := by
      rw [hcosV]; rfl
    have h2 : χ p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) (restrict V' T₀)).cosupp ↔
        ((χ p : openPreimage T₀ V') : Y₀) ∈ (geoTransformAlong 𝔪 T₀).cosupp := by
      rw [hcosV']; rfl
    rw [← h1, ← h2, hcosφ]
    rfl
  refine mem_maxLocus_iff_of _ _ hs fun _ => ?_
  have h5 := MonomialInvariantFunctorialAlong.towerInvAlong_restrict 𝔪 hN h𝔞 V T₀ hTt₀ p
  have h5' := MonomialInvariantFunctorialAlong.towerInvAlong_restrict 𝔪 hN h𝔞 V' T₀ hTt₀ (χ p)
  have h6 := NonmonomialOrderMonomialTransport.towerInvAlong_isTowerIso φ hN' h𝔞' hχ hTtV' p
  rw [hφ] at h6
  show MonomialStepAlong.towerInvAlong 𝔪 T₀ (p : Y₀) =
    MonomialStepAlong.towerInvAlong 𝔪 T₀ ((χ p : openPreimage T₀ V') : Y₀)
  rw [← h5, h6, h5']

end Monomial

/-! ### Concatenations -/

section Append

variable {X : CMfd.{u} n} {V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')

/-- **Equivariance of a concatenation**: if `T₀|_V ≅ T₀|_{V'}` over `φ` with last-stage map `χ₀`, and
`T₁|_{T₀⁻¹V} ≅ T₁|_{T₀⁻¹V'}` over `χ₀`, then `(T₀ T₁)|_V ≅ (T₀ T₁)|_{V'}` over `φ`. -/
theorem exists_isTowerIso_restrict_append {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    {χ₀ : CMfd.of (n := n) (openPreimage T₀ V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T₀ V')} (h₀ : IsTowerIso φ (restrict V T₀) (restrict V' T₀) χ₀)
    {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y)
    {χ₁ : CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ V)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ V'))}
    (h₁ : IsTowerIso χ₀ (restrict (openPreimage T₀ V) T₁) (restrict (openPreimage T₀ V') T₁) χ₁) :
    ∃ χ : CMfd.of (n := n) (openPreimage (T₀.append T₁) V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (T₀.append T₁) V'),
      IsTowerIso φ (restrict V (T₀.append T₁)) (restrict V' (T₀.append T₁)) χ := by
  have a := BlowupTowerIsoTail.isTowerIso_restrict_append V T₀ T₁
  have b := h₀.append h₁
  have c := (BlowupTowerIsoTail.isTowerIso_restrict_append V' T₀ T₁).symm
  exact ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base ((a.trans b).trans c) (Φ' := φ) fun _ => rfl⟩

/-- **Transforms of a natural marked ideal are natural**: if `φ` carries `𝔪|_{V'}` to `𝔪|_V` and `T` is a multiple test
blow-up of `𝔪` with `T|_V ≅ T|_{V'}` over `φ` (last-stage map `χ`), then `χ` carries `𝔪_T|_{T⁻¹V'}` to `𝔪_T|_{T⁻¹V}`. -/
theorem pullback_restrict_geoTransformAlong {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent)
    (hφ : MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) =
      MarkedIdeal.pullback (Subtype.val : V → X) 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    {χ : CMfd.of (n := n) (openPreimage T V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T V')} (hχ : IsTowerIso φ (restrict V T) (restrict V' T) χ) :
    MarkedIdeal.pullback χ (MarkedIdeal.pullback (Subtype.val : openPreimage T V' → Y) (geoTransformAlong 𝔪 T)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T V → Y) (geoTransformAlong 𝔪 T) := by
  have hN' := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN V'
  have h𝔞' := GermIdealPullbackCalculus.isCoherent_pullback (contMDiff_subtype_val (U := V')) h𝔞
  have hTtV' := isGeoTestTower_restrict (U := V') hN h𝔞 T hT
  have h := IsTowerIso.geoTransformAlong_eq (𝔪 := MarkedIdeal.pullback (Subtype.val : V' → X) 𝔪) φ hN' h𝔞' hχ hTtV'
  rw [hφ, geoTransformAlong_restrict V hN h𝔞 T hT, geoTransformAlong_restrict V' hN h𝔞 T hT] at h
  exact h.symm

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)

/-- **Appending a canonical block of a natural marked ideal keeps a tower equivariant**: if `T₀|_V ≅ T₀|_{V'}` over `φ`
with last-stage map `χ₀`, and `𝔫` (on the last stage of `T₀`, in the domain of `R`) is carried by `χ₀` from its restriction
to `T₀⁻¹V'` to its restriction to `T₀⁻¹V`, then for every canonical tower `T₁` of `R.inv 𝔫`,
`(T₀ T₁)|_V ≅ (T₀ T₁)|_{V'}` over `φ`. -/
theorem exists_isTowerIso_restrict_append_of_isCanonical {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    {χ₀ : CMfd.of (n := n) (openPreimage T₀ V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T₀ V')} (h₀ : IsTowerIso φ (restrict V T₀) (restrict V' T₀) χ₀)
    {𝔫 : MarkedIdeal n Y₀} (h𝔫 : IsInvDomain k 𝔫)
    (hnat : MarkedIdeal.pullback χ₀ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ V' → Y₀) 𝔫) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T₀ V → Y₀) 𝔫)
    {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y) (hT₁ : IsCanonical 𝔫 (R.inv 𝔫) T₁) :
    ∃ χ : CMfd.of (n := n) (openPreimage (T₀.append T₁) V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (T₀.append T₁) V'),
      IsTowerIso φ (restrict V (T₀.append T₁)) (restrict V' (T₀.append T₁)) χ := by
  obtain ⟨χ₁, h₁⟩ := exists_isTowerIso_restrict_of_isCanonical R h𝔫 χ₀ hnat T₁ hT₁
  exact exists_isTowerIso_restrict_append φ T₀ h₀ T₁ h₁

/-- **Appending a canonical block of the monomial invariant of a natural marked ideal keeps a tower equivariant.** -/
theorem exists_isTowerIso_restrict_append_of_towerInvAlong {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    {χ₀ : CMfd.of (n := n) (openPreimage T₀ V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T₀ V')} (h₀ : IsTowerIso φ (restrict V T₀) (restrict V' T₀) χ₀)
    {𝔫 : MarkedIdeal n Y₀} (hN : IsClosedSubmanifold n 𝔫.N) (h𝔞 : 𝔫.ideal.IsCoherent)
    (hnat : MarkedIdeal.pullback χ₀ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ V' → Y₀) 𝔫) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T₀ V → Y₀) 𝔫)
    {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y)
    (hT₁ : IsCanonical 𝔫 (fun {Y} Q => MonomialStepAlong.towerInvAlong 𝔫 (Y := Y) Q) T₁)
    (hTt₁ : IsGeoTestTower 𝔫 T₁) :
    ∃ χ : CMfd.of (n := n) (openPreimage (T₀.append T₁) V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (T₀.append T₁) V'),
      IsTowerIso φ (restrict V (T₀.append T₁)) (restrict V' (T₀.append T₁)) χ := by
  obtain ⟨χ₁, h₁⟩ := exists_isTowerIso_restrict_of_towerInvAlong hN h𝔞 χ₀ hnat T₁ hT₁ hTt₁
  exact exists_isTowerIso_restrict_append φ T₀ h₀ T₁ h₁

end Append

end

end Hironaka.HironakaG34CanonicalLocalEquivariance
