import Hironaka.Resolution.HironakaNormalCrossingsHighestPhasePermissions
import Hironaka.Resolution.HironakaCompactCosupportOpenTowerExtension
import Hironaka.Resolution.HironakaNormalCrossingsPermittedFinitePrephase

/-!
# Whole actual history transport of genuine old-branch permissions

Actual open-image charts transport the whole old/current joint family. Real
parent testness supplies the SAME ideal/mark admissibility, and genuine tower
isomorphisms retain every actual slot. No permission follows from endpoint NC.
Blueprint: `hironaka-normal-crossings-joint-permission-transport-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsJointPermissionTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  NormalCrossings NormalCrossingsInvariance NormalCrossingsComparison
  HironakaBaseChange BlowupTowerIsomorphism HironakaNormalCrossingsHighestPhasePermissions
  HironakaNormalCrossingsPermittedFinitePrephase
variable {n : ℕ} {X X' Y Y' Z : CMfd.{u} n}

/-- A genuine open-image coordinate reader transfers whole branch NC data;
actual parent admissibility retains the SAME ideal and mark. -/
theorem local_permission_of_open_embedding
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) {H C : Set X}
    (hC : M.IsAdmissibleCentre C) (M' : MarkedIdeal n X')
    {H' C' : Set X'} {g : X' → X} (hg : IsOpenHoloEmbedding n g)
    (hE : M'.E=M.E.map (g ⁻¹' ·)) (hH : H'=g ⁻¹' H) (hCC : C'=g ⁻¹' C)
    (hcover : C⊆Set.range g) (hp : HasLocalJointBranchCentre M' H' C') :
    HasLocalJointBranchCentre M H C := by
  intro x hx
  obtain ⟨x',hx'⟩ := hcover hx
  have hxC : x'∈C' := by rw [hCC]; change g x'∈C; rwa [hx']
  obtain ⟨V,B,hV,hSNC,hOld,hPerm⟩ := hp x' hxC
  obtain ⟨W,a,hW,ha⟩ := exists_open_image_equiv hg V
  have hxW : x∈W := by change x∈(W : Set X); rw [hW]; exact ⟨x',hV,hx'⟩
  let F := B.map (a.symm ⁻¹' ·)
  have hInv (w : W) : g (a.symm w : X')=(w : X) :=
    (ha (a.symm w)).symm.trans (congrArg Subtype.val (a.apply_symm_apply w))
  have hBoundary : ((MarkedIdeal.pullback (Subtype.val : V → X') M').E).map (a.symm ⁻¹' ·)=
      (MarkedIdeal.pullback (Subtype.val : W → X) M).E := by
    change (M'.E.map ((Subtype.val : V → X') ⁻¹' ·)).map (a.symm ⁻¹' ·)=_
    rw [hE,List.map_map,List.map_map]
    apply List.map_congr_left
    intro D _hD
    ext w
    change g (a.symm w : X')∈D ↔ (w:X)∈D
    rw [hInv]
  have hSNC' := isSNCDivisor_map_preimage (pullsBackCoordinates a.symm) a.symm.continuous hSNC
  rw [List.map_append,hBoundary] at hSNC'
  have hCentre : a.symm ⁻¹' ((Subtype.val : V → X') ⁻¹' C')=
      (Subtype.val : W → X) ⁻¹' C := by
    rw [hCC]
    ext w
    change g (a.symm w : X')∈C ↔ (w:X)∈C
    rw [hInv]
  have hOld' : (Subtype.val : W → X) ⁻¹' H=(⋃ D∈F,D) := by
    ext w
    rw [mem_preimage,mem_iUnion₂]
    constructor
    · intro hw
      have hi : (a.symm w : X')∈H' := by rw [hH]; change g (a.symm w : X')∈H; rwa [hInv]
      have hb : a.symm w∈⋃ D∈B,D := by rw [←hOld]; exact hi
      obtain ⟨D,hD,hwD⟩ := mem_iUnion₂.mp hb
      exact ⟨a.symm ⁻¹' D,List.mem_map.mpr ⟨D,hD,rfl⟩,hwD⟩
    · rintro ⟨D,hDF,hwD⟩
      obtain ⟨A,hAB,hAD⟩ := List.mem_map.mp hDF
      subst D
      have hi : (a.symm w : X')∈H' := by
        change a.symm w∈(Subtype.val : V → X') ⁻¹' H'
        rw [hOld]
        exact mem_iUnion₂.mpr ⟨A,hAB,hwD⟩
      rw [hH] at hi
      change g (a.symm w : X')∈H at hi
      rwa [hInv] at hi
  have hNC := hasNormalCrossings_preimage (pullsBackCoordinates a.symm) (hPerm B (List.Perm.refl B)).2.2
  rw [hCentre,List.map_append,hBoundary] at hNC
  have hCW := IsAdmissibleCentre.pullback_val
    (fun _ _ hmem => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hmem) hC W
  refine ⟨W,F,hxW,hSNC',hOld',fun F' hF => ⟨hCW.1,hCW.2.1,?_⟩⟩
  apply hasNormalCrossings_of_forall_mem hNC
  intro D hD
  rcases List.mem_append.mp hD with hD | hD
  · exact List.mem_append_left _ (hF.mem_iff.mpr hD)
  · exact List.mem_append_right _ hD

private theorem openEmbedding_diffeomorph
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    IsOpenHoloEmbedding n φ := by
  let e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (⊤ : Opens X) :=
    { toEquiv := ⟨fun x => ⟨x,mem_univ x⟩,Subtype.val,fun _ => rfl,fun _ => rfl⟩
      contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk contMDiff_id (fun x => mem_univ x)
      contMDiff_invFun := contMDiff_subtype_val }
  exact ⟨⊤,φ.trans e,fun _ => rfl⟩

private theorem local_permission_pullback
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) {H C : Set X}
    (hC : M.IsAdmissibleCentre C)
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hp : HasLocalJointBranchCentre M H C) :
    HasLocalJointBranchCentre (MarkedIdeal.pullback φ M) (φ ⁻¹' H) (φ ⁻¹' C) := by
  apply local_permission_of_open_embedding (MarkedIdeal.pullback φ M)
    (GermIdealPullbackCalculus.isCoherent_pullback φ.contMDiff hI)
    ((isAdmissibleCentre_pullback_iff (Φ:=φ) hI).mpr hC) M
    (openEmbedding_diffeomorph φ.symm)
  · exact (map_symm_preimage_map_preimage φ M.E).symm
  · exact (symm_preimage_preimage φ H).symm
  · exact (symm_preimage_preimage φ C).symm
  · intro x _hx
    exact ⟨φ x,φ.symm_apply_apply x⟩
  · exact hp

/-- Actual whole tower isomorphisms retain the genuine branch permission at
EVERY centre, with the whole current marked record transported. -/
theorem permissions_pullback_of_towerIso (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) (H : Set X)
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (he : IsTowerIso φ T' T e) :
    IsGeoTestTower M T → HasJointBranchPermissions M H T →
      HasJointBranchPermissions (MarkedIdeal.pullback φ M) (φ ⁻¹' H) T' := by
  induction he with
  | refl => intro _ _; trivial
  | @step Y' Y Z' Z T' T e he C' π' hπ' C π hπ e₁ hcomm hC ih =>
    intro hT hp
    refine ⟨ih hT.1 hp.1,?_⟩
    rw [IsTowerIso.geoTransformAlong_eq φ hN hI he hT.1,he.strictAlong_eq H,←hC]
    exact local_permission_pullback (geoTransformAlong M T)
      (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI T hT.1).2 hT.2 e hp.2

/-- Actual restricted permissions globalize because EVERY ambient test centre
lies over the entire original cosupport, contained in the given actual open. -/
theorem permissions_of_restrict (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) (H : Set X)
    (U : Opens X) (hU : M.cosupp⊆U) :
    ∀ {Y : CMfd.{u} n} (Q : BlowupTower X Y),IsGeoTestTower M Q →
      HasJointBranchPermissions (MarkedIdeal.pullback (Subtype.val : U → X) M)
        ((Subtype.val : U → X) ⁻¹' H) (restrict U Q) →
      HasJointBranchPermissions M H Q
  | _,.refl,_,_ => trivial
  | _,.step Q C π hπ,hQ,hp => by
    refine ⟨permissions_of_restrict M hN hI H U hU Q hQ.1 hp.1,?_⟩
    let V : Opens _ := openPreimage Q U
    have hCurrentI := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hI Q hQ.1).2
    have hpC := hp.2
    change HasLocalJointBranchCentre
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U Q))
      (strictAlong (restrict U Q) ((Subtype.val : U → X) ⁻¹' H))
      ((Subtype.val : V → _) ⁻¹' C) at hpC
    rw [geoTransformAlong_restrict U hN hI Q hQ.1,strictAlong_restrict] at hpC
    apply local_permission_of_open_embedding (X':=CMfd.of (n:=n) V)
      (H':=(Subtype.val : V → _) ⁻¹' strictAlong Q H)
      (C':=(Subtype.val : V → _) ⁻¹' C) (g:=(Subtype.val : V → _))
      (geoTransformAlong M Q) hCurrentI hQ.2
      (MarkedIdeal.pullback (Subtype.val : V → _) (geoTransformAlong M Q))
      (isOpenHoloEmbedding_val V) rfl rfl rfl ?_ hpC
    intro y hy
    have hbase := (HironakaAdmissibleSequence.centresOver_cosupp M hN hI (.step Q C π hπ) hQ).2 hy
    exact ⟨⟨y,hU hbase⟩,rfl⟩

/-- The genuine compact-cosupport extension constructs the SAME ambient
history and derives every old-branch permission from the actual local history. -/
theorem exists_extension_with_permissions (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hK : IsCompact M.cosupp) (H : Set X) (U : Opens X) (hU : M.cosupp⊆U)
    (S : BlowupTower (CMfd.of (n:=n) U) Z)
    (hS : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) S)
    (hp : HasJointBranchPermissions (MarkedIdeal.pullback (Subtype.val : U → X) M)
      ((Subtype.val : U → X) ⁻¹' H) S) :
    ∃ (Y : CMfd.{u} n) (Q : BlowupTower X Y),IsGeoTestTower M Q ∧
      HasJointBranchPermissions M H Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) S (restrict U Q) e := by
  obtain ⟨Y,Q,hQ,e,he⟩ := HironakaCompactCosupportOpenTowerExtension.exists_extension M hN hI hK U hU S hS
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : U → X) M).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hIU : (MarkedIdeal.pullback (Subtype.val : U → X) M).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hI
  have hpU := permissions_pullback_of_towerIso
    (X:=CMfd.of (n:=n) U) (X':=CMfd.of (n:=n) U)
    (MarkedIdeal.pullback (Subtype.val : U → X) M) hNU hIU
    ((Subtype.val : U → X) ⁻¹' H) (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞)
    he.symm hS hp
  change HasJointBranchPermissions
    (MarkedIdeal.pullback (id : U → U) (MarkedIdeal.pullback (Subtype.val : U → X) M))
    ((Subtype.val : U → X) ⁻¹' H) (restrict U Q) at hpU
  rw [ContactCanonicalAlong.pullback_id _ hIU] at hpU
  exact ⟨Y,Q,hQ,permissions_of_restrict M hN hI H U hU Q hQ hpU,e,he⟩

end
end Hironaka.HironakaNormalCrossingsJointPermissionTransport
