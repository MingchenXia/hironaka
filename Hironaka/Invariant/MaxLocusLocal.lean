/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Maximum loci and admissible centres from local data

Source: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 1 of the proof of Proposition `pr:resol`: the invariant at a
point is computed from local data (the invariant of a lower-dimensional marked ideal on a neighbourhood of the
point), and the centre is the locus where the global invariant attains its maximum; "the blow-ups will be performed
at the centers ... for which the invariant attains its maximum".

## Main results

* `maxLocus_comp_strictMono`: a strictly monotone change of values does not change maximum loci;
* `preimage_maxLocus_subset`, **`preimage_maxLocus_eq_or`**: the global centre from local data -- let `ι: Y' → Y`
  (in the application the inclusion of the preimage of a neighbourhood), `s ⊆ Y`, `s' ⊆ ι⁻¹ s` (the cosupport of the
  lower-dimensional marked ideal), `f ∘ ι = φ ∘ g` on `s'` with `φ` strictly monotone, and every other point of `ι⁻¹
  s` strictly below a point of `s'`; then the trace `ι⁻¹ (maxLocus f s)` is empty or the maximum locus of `g` on
  `s'`
* `strictMono_toLex_coe`: the values `(s₀, b)` in `ℕ ×ₗ WithTop Λ` (Step 1 value function) are a strictly monotone
  image of `b`;
* `nestedOpens`, `nestedOpensDiffeo`, `pullback_val_pullback_val`: an open `V ⊆ W` seen inside `W` is biholomorphic to
  `V`, and restricting to `W` and then to `V` is restricting to `V` (transported);
* **`isAdmissibleCentre_pullback_val_of_forall_exists_opens`**: admissible centres are local relative to an open `W`;
* `nestedDiffeo`, `openPreimage_mono`, `mem_openPreimage_restrict_nestedOpens`, `isTowerIso_restrict_nestedOpens`,
  `pullback_symm_nestedOpensDiffeo`, **`restrict_nestedOpens`**: nested open sets of towers -- restricting a tower to `W`
  and then to `W ∩ V` is restricting it to `V ⊆ W` (an isomorphism of towers over `nestedOpensDiffeo`), and for a resolution
  invariant the domain, the canonical segments and the values pass from `𝔫|_W` along `T|_W` to `𝔫|_V` along `T|_V` (for
  shrinking a neighbourhood on which a lower-dimensional marked ideal is formed).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.MaxLocusLocal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

/-! ### Maximum loci of locally given functions -/

section Order

variable {Λ Λ' : Type*} [LinearOrder Λ] [LinearOrder Λ'] {Y Y' : Type*}

/-- **A strictly monotone change of values does not change maximum loci.** -/
theorem maxLocus_comp_strictMono {φ : Λ' → Λ} (hφ : StrictMono φ) (g : Y → Λ') (t : Set Y) :
    maxLocus (φ ∘ g) t = maxLocus g t := by
  ext y
  simp only [maxLocus, mem_ofPred_eq, Function.comp_apply, hφ.le_iff_le]

/-- The trace of a maximum locus lies in the subset `s'` when every other point of the trace of `s` is strictly below a
point of `s'`. -/
theorem preimage_maxLocus_subset (ι : Y' → Y) {f : Y → Λ} {s : Set Y} {s' : Set Y'}
    (hlt : ∀ p ∈ ι ⁻¹' s, p ∉ s' → ∃ q ∈ s', f (ι p) < f (ι q)) (hs' : s' ⊆ ι ⁻¹' s) :
    ι ⁻¹' maxLocus f s ⊆ s' := by
  intro p hp
  by_contra hps
  obtain ⟨q, hq, hpq⟩ := hlt p hp.1 hps
  exact absurd (hp.2 (ι q) (hs' hq)) (not_le.mpr hpq)

/-- **The global centre from local data**: let `s' ⊆ ι⁻¹ s` be a set on which `f ∘ ι = φ ∘ g` with `φ` strictly monotone,
every other point of `ι⁻¹ s` lying strictly below a point of `s'`.  Then the trace of the maximum locus of `f` on `s` is
empty, or it is the maximum locus of `g` on `s'` (when it is nonempty, the global maximum is attained in `s'`, where the
values are those of `g` up to `φ`). -/
theorem preimage_maxLocus_eq_or (ι : Y' → Y) {f : Y → Λ} {g : Y' → Λ'} {φ : Λ' → Λ} (hφ : StrictMono φ)
    {s : Set Y} {s' : Set Y'} (hs' : s' ⊆ ι ⁻¹' s) (hfg : ∀ p ∈ s', f (ι p) = φ (g p))
    (hlt : ∀ p ∈ ι ⁻¹' s, p ∉ s' → ∃ q ∈ s', f (ι p) < f (ι q)) :
    ι ⁻¹' maxLocus f s = ∅ ∨ ι ⁻¹' maxLocus f s = maxLocus g s' := by
  rcases (ι ⁻¹' maxLocus f s).eq_empty_or_nonempty with h | ⟨p₀, hp₀⟩
  · exact Or.inl h
  refine Or.inr ?_
  have hsub := preimage_maxLocus_subset ι hlt hs'
  have hp₀s' := hsub hp₀
  ext p
  constructor
  · intro hp
    have hps' := hsub hp
    refine ⟨hps', fun q hq => ?_⟩
    have := hp.2 (ι q) (hs' hq)
    rw [hfg q hq, hfg p hps'] at this
    exact hφ.le_iff_le.mp this
  · rintro ⟨hps', hp⟩
    refine ⟨hs' hps', fun y hy => ?_⟩
    calc f y ≤ f (ι p₀) := hp₀.2 y hy
      _ = φ (g p₀) := hfg p₀ hp₀s'
      _ ≤ φ (g p) := hφ.monotone (hp p₀ hp₀s')
      _ = f (ι p) := (hfg p hps').symm

/-- **The values `(s₀, b)`** of a lexicographic value function with `WithTop` second component are a strictly monotone image
of `b`. -/
theorem strictMono_toLex_coe {α : Type*} [LinearOrder α] (a : α) :
    StrictMono (fun b : Λ' => toLex (a, (b : WithTop Λ'))) := fun _ _ h =>
  Prod.Lex.toLex_strictMono (Prod.mk_lt_mk_of_le_of_lt le_rfl (WithTop.coe_lt_coe.mpr h))

end Order

/-! ### Admissible centres local relative to an open set -/

section Nested

open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowers

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **An open `V` of `M`, seen inside the open `W`**: the open set `W ∩ V` of `W`. -/
def nestedOpens (W V : Opens M) : Opens W :=
  ⟨(Subtype.val : W → M) ⁻¹' V, V.isOpen.preimage continuous_subtype_val⟩

/-- **For `V ⊆ W`, the open `V` seen inside `W` is biholomorphic to `V`** (the identity on points). -/
def nestedOpensDiffeo {W V : Opens M} (hVW : V ≤ W) :
    CMfd.of (n := n) (nestedOpens W V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V where
  toFun p := ⟨p.1.1, p.2⟩
  invFun q := ⟨⟨q.1, hVW q.2⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
    (contMDiff_subtype_val.comp contMDiff_subtype_val) fun p => p.2
  contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
    (BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val fun q => hVW q.2) fun q => q.2

@[simp] theorem nestedOpensDiffeo_apply {W V : Opens M} (hVW : V ≤ W) (p : nestedOpens W V) :
    ((nestedOpensDiffeo (n := n) hVW p : V) : M) = ((p : W) : M) := rfl

/-- **Restricting to `W` and then to `V ⊆ W` is restricting to `V`**, transported along `nestedOpensDiffeo` (coherent
ideal). -/
theorem pullback_val_pullback_val {𝔪 : MarkedIdeal n M} (h𝔞 : 𝔪.ideal.IsCoherent) {W V : Opens M} (hVW : V ≤ W) :
    MarkedIdeal.pullback (Subtype.val : nestedOpens W V → W) (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪) =
      MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hVW) (MarkedIdeal.pullback (Subtype.val : V → M) 𝔪) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · show (𝔪.E.map ((Subtype.val : W → M) ⁻¹' ·)).map ((Subtype.val : nestedOpens W V → W) ⁻¹' ·) =
      (𝔪.E.map ((Subtype.val : V → M) ⁻¹' ·)).map ((nestedOpensDiffeo (n := n) hVW) ⁻¹' ·)
    rw [List.map_map, List.map_map]
    rfl
  · show GermIdeal.pullback (m := n) (Subtype.val : nestedOpens W V → W)
        (GermIdeal.pullback (m := n) (Subtype.val : W → M) 𝔪.ideal) =
      GermIdeal.pullback (m := n) (nestedOpensDiffeo (n := n) hVW)
        (GermIdeal.pullback (m := n) (Subtype.val : V → M) 𝔪.ideal)
    rw [← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val contMDiff_subtype_val h𝔞,
      ← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val (nestedOpensDiffeo (n := n) hVW).contMDiff h𝔞]
    rfl

/-- **Admissible centres are local relative to an open set**: if every point of the open `W` has an open neighbourhood
`V ⊆ W` such that the trace of `C` on `V` is an admissible centre of `𝔪|_V`, then the trace of `C` on `W` is an admissible
centre of `𝔪|_W` (coherent ideal).  (`ResolutionInvariantDriver.isAdmissibleCentre_of_forall_exists_opens` for `𝔪|_W`,
with the opens of `W` transported by `nestedOpensDiffeo`.) -/
theorem isAdmissibleCentre_pullback_val_of_forall_exists_opens {𝔪 : MarkedIdeal n M} (h𝔞 : 𝔪.ideal.IsCoherent)
    (W : Opens M) {C : Set M}
    (hloc : ∀ x ∈ W, ∃ V : Opens M, x ∈ V ∧ V ≤ W ∧
      (MarkedIdeal.pullback (Subtype.val : V → M) 𝔪).IsAdmissibleCentre ((Subtype.val : V → M) ⁻¹' C)) :
    (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).IsAdmissibleCentre ((Subtype.val : W → M) ⁻¹' C) := by
  have hW : (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞
  refine ResolutionInvariantDriver.isAdmissibleCentre_of_forall_exists_opens (M := CMfd.of (n := n) W)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hW hg) fun p => ?_
  obtain ⟨V, hpV, hVW, hV⟩ := hloc p p.2
  refine ⟨nestedOpens W V, hpV, ?_⟩
  rw [pullback_val_pullback_val h𝔞 hVW]
  have hVc : (MarkedIdeal.pullback (Subtype.val : V → M) 𝔪).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞
  exact (MarkedIdealTowerTransport.isAdmissibleCentre_pullback_iff (Φ := nestedOpensDiffeo (n := n) hVW) hVc).mpr hV

end Nested

/-! ### Nested open sets of towers -/

section NestedTowers

open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerIsomorphism Hironaka.ResolutionInvariantExt
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ}

/-- **Open sets with the same points**: an open `B` of the open `A ⊆ M` and an open `D ⊆ A` of `M` with the same points are
biholomorphic by the identity on points. -/
def nestedDiffeo {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (A : Opens M) (B : Opens A) (D : Opens M) (hBD : ∀ q : A, q ∈ B ↔ (q : M) ∈ D) (hDA : D ≤ A) :
    CMfd.of (n := n) B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) D where
  toFun q := ⟨q.1.1, (hBD q.1).mp q.2⟩
  invFun d := ⟨⟨d.1, hDA d.2⟩, (hBD _).mpr d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
    (contMDiff_subtype_val.comp contMDiff_subtype_val) fun q => (hBD q.1).mp q.2
  contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
    (BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val fun d => hDA d.2) fun d => (hBD _).mpr d.2

variable {X : CMfd.{u} n}

/-- The open preimages are monotone in the open set. -/
theorem openPreimage_mono {Y : CMfd.{u} n} (T : BlowupTower X Y) {V W : Opens X} (hVW : V ≤ W) :
    openPreimage T V ≤ openPreimage T W :=
  fun _ hp => hVW hp

/-- **The open preimage of `W ∩ V` along `T|_W`** has the points of the open preimage of `V` along `T`. -/
theorem mem_openPreimage_restrict_nestedOpens (W V : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (q : openPreimage T W) : q ∈ openPreimage (restrict W T) (nestedOpens W V) ↔ (q : Y) ∈ openPreimage T V := by
  show ((((restrict W T).proj q : W)) : X) ∈ V ↔ T.proj q.1 ∈ V
  rw [proj_restrict]

/-- **Restricting a tower to `W` and then to `W ∩ V` is restricting it to `V ⊆ W`**: the two towers are isomorphic over
`nestedOpensDiffeo` (the identity on points), with last-stage map the identity on points (`nestedDiffeo`). -/
theorem isTowerIso_restrict_nestedOpens {W V : Opens X} (hVW : V ≤ W) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsTowerIso (nestedOpensDiffeo (n := n) hVW) (restrict (nestedOpens W V) (restrict W T)) (restrict V T)
        (nestedDiffeo (openPreimage T W) (openPreimage (restrict W T) (nestedOpens W V)) (openPreimage T V)
          (mem_openPreimage_restrict_nestedOpens W V T) (openPreimage_mono T hVW))
  | _, .refl => BlowupTowerSplitIso.IsTowerIso.congr_last IsTowerIso.refl fun _ => rfl
  | _, .step T _ _ _ => IsTowerIso.step (isTowerIso_restrict_nestedOpens hVW T) _ _ _ (fun _ => rfl) rfl

/-- **Back from `W ∩ V ⊆ W` to `V`**: transporting `(𝔫|_W)|_{W ∩ V}` along the inverse of `nestedOpensDiffeo` gives `𝔫|_V`
(coherent ideal). -/
theorem pullback_symm_nestedOpensDiffeo {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔫 : MarkedIdeal n M} (h𝔞 : 𝔫.ideal.IsCoherent) {W V : Opens M} (hVW : V ≤ W) :
    MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hVW).symm
        (MarkedIdeal.pullback (Subtype.val : nestedOpens W V → W) (MarkedIdeal.pullback (Subtype.val : W → M) 𝔫)) =
      MarkedIdeal.pullback (Subtype.val : V → M) 𝔫 := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · show ((𝔫.E.map ((Subtype.val : W → M) ⁻¹' ·)).map ((Subtype.val : nestedOpens W V → W) ⁻¹' ·)).map
        ((nestedOpensDiffeo (n := n) hVW).symm ⁻¹' ·) = 𝔫.E.map ((Subtype.val : V → M) ⁻¹' ·)
    rw [List.map_map, List.map_map]
    rfl
  · show GermIdeal.pullback (m := n) (nestedOpensDiffeo (n := n) hVW).symm
        (GermIdeal.pullback (m := n) (Subtype.val : nestedOpens W V → W)
          (GermIdeal.pullback (m := n) (Subtype.val : W → M) 𝔫.ideal)) =
      GermIdeal.pullback (m := n) (Subtype.val : V → M) 𝔫.ideal
    rw [← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val contMDiff_subtype_val h𝔞,
      ← GermIdealTotalTransform.pullback_comp (contMDiff_subtype_val.comp contMDiff_subtype_val)
        (nestedOpensDiffeo (n := n) hVW).symm.contMDiff h𝔞]
    rfl

variable {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **A resolution invariant on a smaller open set** (properties (5) and (6) for nested open sets): let `𝔫|_W` lie in the
domain and `T|_W` be a canonical segment of it, and `V ⊆ W` open.  Then `𝔫|_V` lies in the domain, `T|_V` is a canonical
segment of it, and at the points of its cosupport the values of `𝔫|_V` along `T|_V` are those of `𝔫|_W` along `T|_W`
(restriction to `W ∩ V ⊆ W`, then the isomorphism `isTowerIso_restrict_nestedOpens`). -/
theorem restrict_nestedOpens (R : ResolutionInvariant.{u, v} n k Λ) {𝔫 : MarkedIdeal n X}
    (h𝔫 : 𝔫.ideal.IsCoherent) {W V : Opens X} (hVW : V ≤ W)
    (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)
      (R.inv (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)) (restrict W T)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) ∧
      IsCanonical (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫)
        (R.inv (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫)) (restrict V T) ∧
      ∀ p : openPreimage T V,
        p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) (restrict V T)).cosupp →
        R.inv (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) (restrict V T) p =
          R.inv (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T)
            ⟨(p : Y), openPreimage_mono T hVW p.2⟩ := by
  have hdom' := InvDomainTowerAlong.isInvDomain_pullback_val (nestedOpens W V) hdom
  have hcan' := isCanonical_restrict R hdom (nestedOpens W V) (restrict W T) hcan
  have hiso := (isTowerIso_restrict_nestedOpens (X := X) hVW T).symm
  have heq := pullback_symm_nestedOpensDiffeo (M := X) h𝔫 hVW
  have hdomV := InvDomainTowerAlong.isInvDomain_pullback (nestedOpensDiffeo (n := n) hVW).symm hdom'
  rw [heq] at hdomV
  have hcanV := isCanonical_of_isTowerIso R hdom' (nestedOpensDiffeo (n := n) hVW).symm hiso hcan'
  rw [heq] at hcanV
  refine ⟨hdomV, hcanV, fun p hp => ?_⟩
  have hTt' := isGeoTestTower_of_isCanonical R hdom' _ hcan'
  have hcos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hVW).symm
    hdom'.isWellFormed.isClosedSubmanifold_N hdom'.isWellFormed.isCoherent hiso hTt'
  rw [heq] at hcos
  have hp' := hp
  rw [hcos] at hp'
  have key := R.towerIso (nestedOpensDiffeo (n := n) hVW).symm _ hdom' _ _ _ hiso hcan' p hp'
  rw [heq] at key
  rw [key]
  have hTt := isGeoTestTower_of_isCanonical R hdom _ hcan
  have hp'' := hp'
  rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent (nestedOpens W V) (restrict W T) hTt] at hp''
  exact R.restrictOpen _ hdom (nestedOpens W V) (restrict W T) hcan
    ((nestedDiffeo (openPreimage T W) (openPreimage (restrict W T) (nestedOpens W V)) (openPreimage T V)
      (mem_openPreimage_restrict_nestedOpens W V T) (openPreimage_mono T hVW)).symm p) hp''

end NestedTowers

end

end Hironaka.MaxLocusLocal
