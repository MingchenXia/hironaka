import Hironaka.Invariant.SmoothCentreInvariant
import Hironaka.Invariant.CanonicalCentres

/-! Actual nested-plane translations on a proper carrier and native
reflexive value homogeneity. The held translation/pullback engines are reused
with no duplicate engine credit. Blueprint FIRST. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Metric
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothNestedCentreHomogeneity
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowerTransforms BlowupTowerIsomorphism SmoothCentreHomogeneity
  NormalDerivativeChart BlowupFlatCoordinates NormalCrossings
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n} {L Z : Set X} {x : X}

private theorem add_mem_coordSubspace_iff {S : Finset (Fin n)} {z v : ComplexModel n}
    (hv : v∈coordSubspace S) : z+v∈coordSubspace S ↔ z∈coordSubspace S := by
  constructor
  · intro h i hi
    have h1:=h i hi
    simp only [PiLp.add_apply] at h1
    rwa [hv i hi,add_zero] at h1
  · intro h i hi
    simp only [PiLp.add_apply]
    rw [h i hi,hv i hi,add_zero]

theorem exists_nested_translation
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (SL SZ : Finset (Fin n)) (hsubset : SL ⊆ SZ)
    (hL : ∀ y∈flatDomain Φ, y∈L ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace SL)
    (hZ : ∀ y∈flatDomain Φ, y∈Z ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace SZ) :
    ∃ W : Set X, IsOpen W ∧ x∈W ∧ ∀ y∈Z∩W,
      ∃ (U1 U2 : Opens X)
        (χ : CMfd.of (n:=n) U1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n:=n) U2)
        (hx : x∈U1),
        y∈U2 ∧ ((χ ⟨x,hx⟩ : U2) : X)=y ∧
        (∀ p : U1, ((χ p : U2) : X)∈Z ↔ (p : X)∈Z) ∧
        (∀ p : U1, ((χ p : U2) : X)∈L ↔ (p : X)∈L) := by
  let c : NormalDerivativeChart.FlatChart n (univ : Set X) x n :=
    ⟨Φ,hsrc,hzero,fun {_y} _hy _hyΦ => by
      constructor
      · intro _h i hi
        exact False.elim ((Nat.not_le_of_lt i.isLt) hi)
      · intro _h
        trivial⟩
  -- the good neighbourhood `A` of `x`
  obtain ⟨A, hAsub, hAo, hxA⟩ := mem_nhds_iff.mp
    ((c.eventually_mdifferentiableAt_ψ.and c.eventually_inv_ψ).and c.eventually_mem_flatDomain)
  have hψA : ∀ y ∈ A, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.ψ y := fun y hy =>
    (hAsub hy).1.1
  have hinvψ : ∀ y ∈ A, c.inv (c.ψ y) = y := fun y hy => (hAsub hy).1.2
  have hflat : ∀ y ∈ A, (y ∈ Z ↔ c.ψ y ∈ coordSubspace SZ) := fun y hy =>
    hZ y (hAsub hy).2
  have hflatL : ∀ y ∈ A, (y ∈ L ↔ c.ψ y ∈ coordSubspace SL) := fun y hy =>
    hL y (hAsub hy).2
  -- the good ball around `0`
  have hB : ∀ᶠ w in 𝓝 (0 : ComplexModel n),
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.inv w ∧ c.ψ (c.inv w) = w ∧ c.inv w ∈ A :=
    c.eventually_mdifferentiableAt_inv.and (c.eventually_ψ_inv.and (c.tendsto_inv.eventually (hAo.mem_nhds hxA)))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hB
  set r := ρ / 2 with hr
  have hr0 : 0 < r := by positivity
  have h2r : ∀ w : ComplexModel n, ‖w‖ < 2 * r →
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.inv w ∧ c.ψ (c.inv w) = w ∧ c.inv w ∈ A :=
    fun w hw => hρsub (mem_ball_zero_iff.mpr (by rw [hr] at hw; linarith))
  have hψc : ContinuousOn c.ψ A := fun y hy => (hψA y hy).continuousAt.continuousWithinAt
  -- the open sets
  let UB : ComplexModel n → Opens X := fun v => ⟨A ∩ c.ψ ⁻¹' ball v r, hψc.isOpen_inter_preimage hAo isOpen_ball⟩
  refine ⟨UB 0, (UB 0).isOpen, ⟨hxA, by simp [c.ψ_self, hr0]⟩, fun x' hx' => ?_⟩
  obtain ⟨hx'Z, hx'A, hx'B⟩ := hx'
  set v := c.ψ x' with hv
  have hvP : v ∈ coordSubspace SZ := (hflat x' hx'A).mp hx'Z
  have hvL : v ∈ coordSubspace SL := fun i hi => hvP i (hsubset hi)
  have hvr : ‖v‖ < r := mem_ball_zero_iff.mp hx'B
  -- the translation and its inverse
  have hfwd : ∀ y ∈ UB 0, ‖c.ψ y + v‖ < 2 * r := fun y hy => by
    have h1 : ‖c.ψ y‖ < r := mem_ball_zero_iff.mp hy.2
    calc ‖c.ψ y + v‖ ≤ ‖c.ψ y‖ + ‖v‖ := norm_add_le _ _
      _ < 2 * r := by linarith
  have hbwd : ∀ q ∈ UB v, ‖c.ψ q - v‖ < 2 * r := fun q hq => by
    have h1 : ‖c.ψ q - v‖ < r := mem_ball_iff_norm.mp hq.2
    linarith
  obtain ⟨Φ, hΦ, -⟩ := exists_diffeomorph_opens_of_mapsTo (U := UB 0) (V := UB v)
    (φ := fun y => c.inv (c.ψ y + v)) (ψ := fun q => c.inv (c.ψ q - v))
    (fun y hy => ⟨(h2r _ (hfwd y hy)).2.2, by
      show c.ψ (c.inv (c.ψ y + v)) ∈ ball v r
      rw [(h2r _ (hfwd y hy)).2.1, mem_ball_iff_norm, add_sub_cancel_right]
      exact mem_ball_zero_iff.mp hy.2⟩)
    (fun q hq => ⟨(h2r _ (hbwd q hq)).2.2, by
      show c.ψ (c.inv (c.ψ q - v)) ∈ ball 0 r
      rw [(h2r _ (hbwd q hq)).2.1, mem_ball_zero_iff]
      exact mem_ball_iff_norm.mp hq.2⟩)
    (fun y hy => by
      have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (fun y => c.ψ y + v) y :=
        ((differentiableAt_id.add_const v).mdifferentiableAt).comp y (hψA y hy.1)
      have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (c.inv ∘ fun y => c.ψ y + v) y :=
        (h2r _ (hfwd y hy)).1.comp y h1
      exact h2)
    (fun q hq => by
      have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (fun q => c.ψ q - v) q :=
        ((differentiableAt_id.sub_const v).mdifferentiableAt).comp q (hψA q hq.1)
      have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (c.inv ∘ fun q => c.ψ q - v) q :=
        (h2r _ (hbwd q hq)).1.comp q h1
      exact h2)
    (fun y hy => by
      show c.inv (c.ψ (c.inv (c.ψ y + v)) - v) = y
      rw [(h2r _ (hfwd y hy)).2.1, add_sub_cancel_right, hinvψ y hy.1])
    (fun q hq => by
      show c.inv (c.ψ (c.inv (c.ψ q - v)) + v) = q
      rw [(h2r _ (hbwd q hq)).2.1, sub_add_cancel, hinvψ q hq.1])
  have hxU : x ∈ UB 0 := ⟨hxA, by simp [c.ψ_self, hr0]⟩
  refine ⟨UB 0, UB v, Φ, hxU, ⟨hx'A, by show c.ψ x' ∈ ball v r; rw [hv]; exact mem_ball_self hr0⟩, ?_, ?_, ?_⟩
  · rw [hΦ]
    show c.inv (c.ψ x + v) = x'
    rw [c.ψ_self, zero_add, hv, hinvψ x' hx'A]
  · intro p
    rw [hΦ]
    have hpA : (p : X) ∈ A := p.2.1
    have hq := (h2r _ (hfwd p p.2))
    rw [hflat _ hq.2.2, hflat _ hpA, hq.2.1, add_mem_coordSubspace_iff hvP]

  · intro p
    rw [hΦ]
    have hpA : (p : X) ∈ A := p.2.1
    have hq := (h2r _ (hfwd p p.2))
    rw [hflatL _ hq.2.2, hflatL _ hpA, hq.2.1, add_mem_coordSubspace_iff hvL]

theorem exists_nested_marked_homogeneity
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (SL SZ : Finset (Fin n)) (hsubset : SL ⊆ SZ)
    (hL : ∀ y∈flatDomain Φ, y∈L ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace SL)
    (hZ : ∀ y∈flatDomain Φ, y∈Z ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace SZ)
    (d : ℕ) :
    ∃ W : Set X, IsOpen W ∧ x∈W ∧ ∀ y∈Z∩W,
      ∃ (U1 U2 : Opens X)
        (χ : CMfd.of (n:=n) U1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n:=n) U2)
        (hx : x∈U1),
        y∈U2 ∧ ((χ ⟨x,hx⟩ : U2) : X)=y ∧
        (∀ p : U1, ((χ p : U2) : X)∈Z ↔ (p : X)∈Z) ∧
        (∀ p : U1, ((χ p : U2) : X)∈L ↔ (p : X)∈L) ∧
        MarkedIdeal.pullback χ
          (MarkedIdeal.pullback (Subtype.val : U2→X)
            (⟨L,[],vanishingIdeal (n:=n) Z,d⟩ : MarkedIdeal n X)) =
          MarkedIdeal.pullback (Subtype.val : U1→X)
            (⟨L,[],vanishingIdeal (n:=n) Z,d⟩ : MarkedIdeal n X) := by
  obtain ⟨W,hWo,hxW,hW⟩:=exists_nested_translation Φ hsrc hzero SL SZ hsubset hL hZ
  refine ⟨W,hWo,hxW,?_⟩
  intro y hy
  obtain ⟨U1,U2,χ,hx,hyU,hχ,hχZ,hχL⟩:=hW y hy
  exact ⟨U1,U2,χ,hx,hyU,hχ,hχZ,hχL,
    pullback_pullback_val_smoothCentreMarked d χ hχZ hχL⟩

theorem native_flat_nested_value_homogeneity
    (hZc : IsClosed Z) (hZL : Z ⊆ L)
    (hdom : IsInvDomain n (⟨L,[],vanishingIdeal (n:=n) Z,1⟩ : MarkedIdeal n X))
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (SL SZ : Finset (Fin n)) (hsubset : SL ⊆ SZ)
    (hL : ∀ y∈flatDomain Φ, y∈L ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace SL)
    (hZ : ∀ y∈flatDomain Φ, y∈Z ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace SZ) :
    ∃ W : Set X, IsOpen W ∧ x∈W ∧ ∀ y∈Z∩W,
      (CanonicalCentres.canonicalInvariant n).inv
        (⟨L,[],vanishingIdeal (n:=n) Z,1⟩ : MarkedIdeal n X)
        (BlowupTower.refl : BlowupTower X X) y =
      (CanonicalCentres.canonicalInvariant n).inv
        (⟨L,[],vanishingIdeal (n:=n) Z,1⟩ : MarkedIdeal n X)
        (BlowupTower.refl : BlowupTower X X) x := by
  let M : MarkedIdeal n X:=⟨L,[],vanishingIdeal (n:=n) Z,1⟩
  let R:=CanonicalCentres.canonicalInvariant n
  have hcos : M.cosupp=Z:=SmoothCentreLocus.cosupp_vanishingIdeal hZc hZL
  have hxZ : x∈Z := by
    apply (hZ x (mem_flatDomain_self Φ)).mpr
    intro i _hi
    rw [hzero]
    rfl
  obtain ⟨W,hWo,hxW,hW⟩:=exists_nested_marked_homogeneity Φ hsrc hzero SL SZ hsubset hL hZ 1
  refine ⟨W,hWo,hxW,?_⟩
  intro y hy
  obtain ⟨U1,U2,χ,hxU,hyU,hχ,_hχZ,_hχL,hpb⟩:=hW y hy
  have hhol:=MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hdom.isWellFormed.isCoherent
  have h1:=R.isInvValue.restrictOpen M hdom U1 BlowupTower.refl trivial ⟨x,hxU⟩
    (by show x∈M.cosupp;rw [hcos];exact hxZ)
  have h2:=R.isInvValue.restrictOpen M hdom U2 BlowupTower.refl trivial ⟨y,hyU⟩
    (by show y∈M.cosupp;rw [hcos];exact hy.1)
  have hdom2:=InvDomainTowerAlong.isInvDomain_pullback_val U2 hdom
  have hc2 : χ ⟨x,hxU⟩∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U2→X) M)
      (BlowupTower.refl : BlowupTower (CMfd.of (n:=n) U2) (CMfd.of (n:=n) U2))).cosupp := by
    show χ ⟨x,hxU⟩∈(MarkedIdeal.pullback (Subtype.val : U2→X) M).cosupp
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val M hhol U2,hcos]
    change ((χ ⟨x,hxU⟩ : U2) : X)∈Z
    rw [hχ]
    exact hy.1
  have h3:=R.isInvValue.towerIso χ (MarkedIdeal.pullback (Subtype.val : U2→X) M) hdom2
    BlowupTower.refl BlowupTower.refl χ IsTowerIso.refl trivial ⟨x,hxU⟩ hc2
  change MarkedIdeal.pullback χ (MarkedIdeal.pullback (Subtype.val : U2→X) M)=
    MarkedIdeal.pullback (Subtype.val : U1→X) M at hpb
  rw [hpb] at h3
  have hχ' : χ ⟨x,hxU⟩=⟨y,hyU⟩:=Subtype.ext hχ
  rw [hχ'] at h3
  exact h2.symm.trans (h3.symm.trans h1)

end
end Hironaka.HironakaSmoothNestedCentreHomogeneity
