import Hironaka.Invariant.MonomialResolution
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The invariant of the monomial case under open restrictions, biholomorphisms and empty blowups

Blueprint `hir:monomial-invariance` (`blueprint/src/hironaka.tex`, Hironaka phase H4; clause (4) of `hir:monomial-case`,
`N = M`).  Sources: Włodarczyk 2005, Step 2b and §2.4 (functoriality for étale maps); Bierstone--Milman 2008, §5 and
Theorem 1.3 (the invariant depends only on the exponents of the members through the point and their order in `E`).

The invariant `γ = MonomialCase.gamma 𝔞 E d` at `x` is read off the members of `E` through `x` and the exponents
`e_{E_i}(x) = DivisorExponent.divExp 𝔞 (E_i) x`, which are defined by the cosupports `cosupp(𝔞, e)` near `x`.

* `isDivNear_pullback_iff`, `divExp_pullback`, `gamma_pullback`: for a map `φ : M' → M` along which the cosupports pull
  back (`cosupp(φ^*𝔞, e) = φ⁻¹ cosupp(𝔞, e)`) and which maps neighbourhoods of `x'` onto neighbourhoods of `φ x'`, the
  exponents and the invariant of `(φ^*𝔞, φ⁻¹E)` at `x'` are those of `(𝔞, E)` at `φ x'`;
* `gamma_pullback_val` (**restriction to an open set**) and `gamma_pullback_diffeomorph` (**biholomorphisms**) for marked
  ideals, `MarkedIdealBiholomorphism.MarkedIdeal.pullback`;
* `gamma_geoTransform_empty` (**steps with empty centre**): for the blowup along `∅` (a biholomorphism) the invariant of
  the transform is the invariant of the base read through `π` (the appended member passes through no point);
* `towerInv_restrict`, `towerInv_transport`: along the restriction of a multiple test blow-up to an open set
  (`MarkedIdealRestrictOpen`) and along the transport of a tower by a biholomorphism of the base
  (`MarkedIdealTowerTransport`), the invariants at the stages correspond.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MonomialInvariantFunctorial

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.DivisorExponent
  Hironaka.MonomialPart Hironaka.MonomialCase
  Hironaka.MonomialResolution Hironaka.MonomialInvariant
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealTowerTransport
  Hironaka.NormalCrossings

noncomputable section

variable {n : ℕ}

/-! ### Exponents and the invariant along maps that pull back cosupports -/

section Pullback

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {φ : M' → M} {𝔞 : GermIdeal n M}
  (hcos : ∀ e, cosupport n univ (GermIdeal.pullback (m := n) φ 𝔞) e = φ ⁻¹' cosupport n univ 𝔞 e)
  {x' : M'} (hmap : Filter.map φ (𝓝 x') = 𝓝 (φ x'))
include hcos hmap

/-- **Divisibility along a member pulls back.** -/
theorem isDivNear_pullback_iff (H : Set M) (e : ℕ) :
    IsDivNear n (GermIdeal.pullback (m := n) φ 𝔞) (φ ⁻¹' H) e x' ↔ IsDivNear n 𝔞 H e (φ x') := by
  show (∀ᶠ z in 𝓝 x', z ∈ φ ⁻¹' H → z ∈ cosupport n univ (GermIdeal.pullback (m := n) φ 𝔞) e) ↔
    ∀ᶠ z in 𝓝 (φ x'), z ∈ H → z ∈ cosupport n univ 𝔞 e
  rw [hcos e, ← hmap, Filter.eventually_map]
  rfl

open Classical in
/-- **The exponent along a member pulls back**: `e_{φ⁻¹H}(φ^*𝔞)(x') = e_H(𝔞)(φ x')`. -/
theorem divExp_pullback (H : Set M) :
    divExp n (GermIdeal.pullback (m := n) φ 𝔞) (φ ⁻¹' H) x' = divExp n 𝔞 H (φ x') := by
  have hP : (fun e => IsDivNear n (GermIdeal.pullback (m := n) φ 𝔞) (φ ⁻¹' H) e x') =
      fun e => IsDivNear n 𝔞 H e (φ x') := funext fun e => propext (isDivNear_pullback_iff hcos hmap H e)
  unfold divExp
  show (if h : ∃ e, ¬ (fun e => IsDivNear n (GermIdeal.pullback (m := n) φ 𝔞) (φ ⁻¹' H) e x') (e + 1)
      then Nat.find h else 0) = (if h : ∃ e, ¬ (fun e => IsDivNear n 𝔞 H e (φ x')) (e + 1) then Nat.find h else 0)
  rw [hP]

omit hcos hmap in
/-- The members of `φ⁻¹E` through `x'` are those of `E` through `φ x'`. -/
theorem memberIdx_map_preimage (E : List (Set M)) (x' : M') :
    memberIdx (E.map (φ ⁻¹' ·)) x' = memberIdx E (φ x') := by
  ext i
  rw [mem_memberIdx, mem_memberIdx]
  constructor
  · rintro ⟨hi, hx⟩
    refine ⟨by simpa using hi, ?_⟩
    simpa using hx
  · rintro ⟨hi, hx⟩
    refine ⟨by simpa using hi, ?_⟩
    simpa using hx

/-- **The invariant pulls back**: `γ(φ^*𝔞, φ⁻¹E, d)(x') = γ(𝔞, E, d)(φ x')`. -/
theorem gamma_pullback (E : List (Set M)) (d : ℕ) :
    gamma n (GermIdeal.pullback (m := n) φ 𝔞) (E.map (φ ⁻¹' ·)) d x' = gamma n 𝔞 E d (φ x') := by
  unfold gamma
  rw [memberIdx_map_preimage]
  congr 1
  funext i
  unfold expData
  by_cases hi : i < E.length
  · have hi' : i < (E.map (φ ⁻¹' ·)).length := by simpa using hi
    rw [dif_pos hi', dif_pos hi]
    have hget : (E.map (φ ⁻¹' ·)).get ⟨i, hi'⟩ = φ ⁻¹' E.get ⟨i, hi⟩ := by simp
    rw [hget]
    exact divExp_pullback hcos hmap _
  · have hi' : ¬ i < (E.map (φ ⁻¹' ·)).length := by simpa using hi
    rw [dif_neg hi', dif_neg hi]

end Pullback

/-! ### Open restrictions, biholomorphisms, empty centres -/

section Marked

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Restriction to an open set** (`hir:monomial-case` (4)): the invariant of `𝔪|_U` at `p` is that of `𝔪` at `p`. -/
theorem gamma_pullback_val (𝔪 : MarkedIdeal n X) (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x)
    (U : Opens X) (p : U) (d : ℕ) :
    gamma n (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).E
      d p = gamma n 𝔪.ideal 𝔪.E d p.1 := by
  refine gamma_pullback (φ := (Subtype.val : U → X)) (fun e => ?_) ?_ 𝔪.E d
  · have h := MarkedIdealRestrictOpen.cosupp_pullback_val (⟨univ, [], 𝔪.ideal, e⟩ : MarkedIdeal n X) h𝔞 U
    exact h
  · exact map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (U : Set X)) p.2 (U.isOpen.mem_nhds p.2)

/-- **Biholomorphisms** (`hir:monomial-case` (4)): for a biholomorphism `Φ : X' ≅ X`, the invariant of `Φ^*𝔪` at `p` is
that of `𝔪` at `Φ p`. -/
theorem gamma_pullback_diffeomorph {X' : Type u} [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X']
    [IsComplexManifold n X'] (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (𝔪 : MarkedIdeal n X)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (p : X') (d : ℕ) :
    gamma n (MarkedIdeal.pullback Φ 𝔪).ideal (MarkedIdeal.pullback Φ 𝔪).E d p = gamma n 𝔪.ideal 𝔪.E d (Φ p) := by
  refine gamma_pullback (φ := Φ) (fun e => ?_) ?_ 𝔪.E d
  · exact MarkedIdeal.cosupp_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply
      (⟨univ, [], 𝔪.ideal, e⟩ : MarkedIdeal n X) h𝔞
  · exact Φ.toHomeomorph.map_nhds_eq p

/-- **Steps with empty centre** (`hir:monomial-case` (4)): for the blowup `π` along `∅` the invariant of the transform
of a monomial `(X, X, E, 𝔞, d)` is that of `𝔪` read through `π` (`MonomialResolution.gamma_geoTransform_eq_of_notMem`). -/
theorem gamma_geoTransform_empty (hn : 0 < n) {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {π : Y → X} (hπ : IsBlowupAlong n (∅ : Set X) π) (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ)
    (hE : IsSNCDivisor n 𝔪.E) (h𝔞 : 𝔪.ideal.IsCoherent) (hmono : (monomialPart n 𝔪.ideal 𝔪.E).Le 𝔪.ideal)
    (z : Y) (d : ℕ) :
    gamma n (𝔪.geoTransform ∅ π).ideal (𝔪.geoTransform ∅ π).E d z = gamma n 𝔪.ideal 𝔪.E d (π z) := by
  have h𝔞' : (𝔪.geoTransform ∅ π).ideal.IsCoherent := by
    rw [geoTransform_ideal_eq_controlledTransform hN h𝔞 hπ]
    refine BlowupControlledTransform.isCoherent_controlledTransform hπ h𝔞 ?_
    exact HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hπ.1 (empty_subset _)
  exact gamma_geoTransform_eq_of_notMem hn hπ 𝔪 hN hE h𝔞 h𝔞' hmono (notMem_empty (π z)) d

end Marked

/-! ### Along restricted and transported towers -/

section Tower

variable {X : CMfd.{u} n}

/-- **The invariant along a restricted tower** (`hir:monomial-case` (4), with `hir:open-restriction-tower`): along the
restriction to `U` of a multiple test blow-up `T` of `𝔪`, the invariant of the transform of `𝔪|_U` at `p` is the
invariant of the transform of `𝔪` at `p`. -/
theorem towerInv_restrict (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (p : openPreimage T U) :
    towerInv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = towerInv 𝔪 T p.1 := by
  obtain ⟨-, hcT⟩ := MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  unfold towerInv
  rw [MarkedIdealRestrictOpen.geoTransformAlong_restrict U hN h𝔞 T hT]
  exact gamma_pullback_val (geoTransformAlong 𝔪 T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) (openPreimage T U) p _

/-- **The invariant along a transported tower** (`hir:monomial-case` (4), with `hir:tower-transport`): for a
biholomorphism `Φ : X' ≅ X` and a tower `T` over `X`, the invariant of the transform of `Φ^*𝔪` along the transported
tower at `p` is the invariant of the transform of `𝔪` along `T` at `back p`. -/
theorem towerInv_transport {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (𝔪 : MarkedIdeal n X) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → ∀ p : (transport Φ T).target,
      towerInv (MarkedIdeal.pullback Φ 𝔪) (transport Φ T).tower p = towerInv 𝔪 T ((transport Φ T).back p)
  | _, .refl, p => gamma_pullback_diffeomorph Φ 𝔪
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) p _
  | _, .step T C π hπ, p => by
      unfold towerInv
      rw [geoTransformAlong_transport_step Φ h𝔞 T C π hπ]
      rfl

end Tower

end

end Hironaka.MonomialInvariantFunctorial
