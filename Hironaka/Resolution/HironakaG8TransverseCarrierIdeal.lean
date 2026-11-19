import Hironaka.Resolution.HironakaActualExceptionalCarrierGeometry
import Hironaka.Blowup.BlowupStrictIdeal

/-! Whole ordinary transverse carrier ideal pullback.
Blueprint: hironaka-g8-resume-transverse-carrier-ideal.tex (restored from the archived 2026-11-09 draft). -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8TransverseCarrierIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings SimultaneousNormalCrossings BlowupStrictSubmanifold
  BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupFibreDirection
  BlowupSNCTransform BlowupStrictIdeal RelativePrincipalizationSpan RegularAtDimTransport
variable {n : ℕ} {X Y : CMfd.{0} n}

def linearCoordinatesAt (q : ComplexModel n)
    (L : ComplexModel n ≃L[ℂ] ComplexModel n) : LocalHolomorphicEquivAt (n:=n) q where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := L
  invFun := L.symm
  toFun_holomorphic := L.differentiable.differentiableOn
  invFun_holomorphic := L.symm.differentiable.differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => L.symm_apply_apply _
  right_inv := fun _ _ => L.apply_symm_apply _

def permutationMap (s : Fin n ≃ Fin n) : ComplexModel n ≃L[ℂ] ComplexModel n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ s).toContinuousLinearEquiv

theorem permutation_apply (s : Fin n ≃ Fin n) (w : ComplexModel n) (a : Fin n) :
    permutationMap s w (s a)=w a := by
  simp [permutationMap,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

theorem permutation_subspace (s : Fin n ≃ Fin n) (A : Finset (Fin n))
    (w : ComplexModel n) :
    permutationMap s w ∈ coordSubspace (A.map s.toEmbedding) ↔ w∈coordSubspace A := by
  constructor
  · intro h a ha
    simpa only [permutation_apply] using h (s a) (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
  · intro h a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp ha
    change permutationMap s w (s b) = 0
    rw [permutation_apply]
    exact h b hb

-- H1: arbitrary normal sets and arbitrary points in the actual chart domain.
theorem mem_vanishingIdeal_iff_coordinate_span
    {x : X} (Phi : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (hsrc : Phi.source ⊆ (chartAt (ComplexModel n) x).target)
    (A : Finset (Fin n)) (N : Set X)
    (hflat : ∀ {u : X}, u∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x u∈Phi.source →
      (u∈N ↔ Phi.toFun (chartAt (ComplexModel n) x u)∈coordSubspace A))
    {u : X} (hu : u∈flatDomain Phi) (g : X→ℂ) :
    (vanishingIdeal (n:=n) N).mem u g ↔
      IsInSpanAt (n:=n)
        (fun f => f∈Set.range (fun a : Fin n =>
          if a∈A then flatCoord Phi a else fun _ => (0:ℂ))) u g := by
  obtain ⟨s,hs⟩ := exists_perm_nested (X:=A) (Y:=A) subset_rfl
  let Psi := LocalHolomorphicEquivAt.comp Phi
    (linearCoordinatesAt (Phi.toFun (chartAt (ComplexModel n) x x)) (permutationMap s)) rfl
  have hPsiSrc : Psi.source ⊆ (chartAt (ComplexModel n) x).target := fun _ h => hsrc h.1
  have hPsiFlat : ∀ {v : X}, v∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x v∈Psi.source →
      (v∈N ↔ Psi.toFun (chartAt (ComplexModel n) x v)∈complexCoordinatePlane n (n-A.card)) := by
    intro v hv hvP
    rw [hflat hv hvP.1]
    change _ ↔ permutationMap s (Phi.toFun _)∈complexCoordinatePlane n (n-A.card)
    constructor
    · intro h a ha
      obtain ⟨b,rfl⟩ := s.surjective a
      rw [permutation_apply]
      exact h b ((hs b).1.mp ha)
    · intro h a ha
      rw [←permutation_apply s _ a]
      exact h (s a) ((hs a).1.mpr ha)
  have huP : u∈flatDomain Psi := ⟨hu.1,hu.2,mem_univ _⟩
  constructor
  · intro hg
    obtain ⟨b,hb0,hbh,hbeq⟩ := exists_eq_sum_flatCoord Psi hPsiSrc hPsiFlat huP hg
    refine ⟨hg.1,n,(fun a => if s.symm a∈A then flatCoord Phi (s.symm a) else fun _ => 0),
      b,fun a => ⟨s.symm a,rfl⟩,hbh,?_⟩
    filter_upwards [hbeq] with v hv
    rw [hv]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : s.symm a∈A
    · simp only [ha,if_true]
      congr 1
    · have halt : a.val<n-A.card := by
        have := (hs (s.symm a)).1
        simp only [s.apply_symm_apply] at this
        exact Nat.lt_of_not_le fun h => ha (this.mp h)
      simp [ha,hb0 a halt]
  · intro hg
    apply mem_vanishingIdeal_of_isInSpanAt' ?_ hg
    rintro f ⟨a,rfl⟩
    by_cases ha : a∈A
    · simp only [ha,if_true]
      refine ⟨holomorphicAt_flatCoord Phi a hu,?_⟩
      filter_upwards [(isOpen_flatDomain Phi).mem_nhds hu] with v hv hvN
      exact (hflat hv.1 hv.2).mp hvN a ha
    · simp only [ha,if_false]
      exact ⟨holomorphicAt_const 0,Eventually.of_forall fun _ _ => rfl⟩

-- H2: the whole span, with every holomorphic target coefficient.
set_option linter.unusedVariables false in
theorem mem_vanishingIdeal_le_pullback_of_matching_normal_coordinates
    {x : X} {y : Y} {pi : Y→X}
    (hpi : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ pi)
    (hxy : pi y=x)
    (Phi : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (Theta : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) y y))
    (hsrc : Phi.source ⊆ (chartAt (ComplexModel n) x).target)
    (htgt : Theta.source ⊆ (chartAt (ComplexModel n) y).target)
    (A : Finset (Fin n)) (N : Set X) (T : Set Y)
    (hN : ∀ {u : X}, u∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x u∈Phi.source →
      (u∈N ↔ Phi.toFun (chartAt (ComplexModel n) x u)∈coordSubspace A))
    (hT : ∀ {u : Y}, u∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y u∈Theta.source →
      (u∈T ↔ Theta.toFun (chartAt (ComplexModel n) y u)∈coordSubspace A))
    (heq : ∀ a∈A, flatCoord Theta a =ᶠ[𝓝 y] (flatCoord Phi a ∘ pi))
    {g : Y→ℂ} (hg : (vanishingIdeal (n:=n) T).mem y g) :
    (GermIdeal.pullback (m:=n) pi (vanishingIdeal (n:=n) N)).mem y g := by
  apply GermIdeal.mem_pullback_iff.mpr
  apply IsInSpanAt.trans ?_
    ((mem_vanishingIdeal_iff_coordinate_span Theta htgt A T hT (mem_flatDomain_self Theta) g).mp hg)
  rintro f ⟨a,rfl⟩
  by_cases ha : a∈A
  · simp only [ha,if_true]
    have hmem : (vanishingIdeal (n:=n) N).mem (pi y) (flatCoord Phi a) := by
      rw [hxy]
      refine ⟨holomorphicAt_flatCoord Phi a (mem_flatDomain_self Phi),?_⟩
      filter_upwards [(isOpen_flatDomain Phi).mem_nhds (mem_flatDomain_self Phi)] with v hv hvN
      exact (hN hv.1 hv.2).mp hvN a ha
    exact isInSpanAt_of_eq_mul ⟨flatCoord Phi a,hmem,rfl⟩
      (holomorphicAt_flatCoord Theta a (mem_flatDomain_self Theta)) (holomorphicAt_const 1)
      (by filter_upwards [heq a ha] with v hv; simpa using hv)
  · simp only [ha,if_false]
    exact isInSpanAt_zero

-- H3: actual matching charts, constructed independently of any log factory.
set_option linter.unusedVariables false in
theorem exists_matching_transverse_normal_coordinates
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E)
    (i j : Fin E.length) (hij : i≠j) (pi : Y→X)
    (hpi : IsBlowupAlong n (E.get i∩E.get j) pi)
    (y : Y) (hyN : pi y∈N) (hyC : pi y∈E.get i∩E.get j) :
    ∃ (A : Finset (Fin n))
      (Phi : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) (pi y) (pi y)))
      (Theta : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) y y)),
      Phi.source ⊆ (chartAt (ComplexModel n) (pi y)).target ∧
      Theta.source ⊆ (chartAt (ComplexModel n) y).target ∧
      (∀ {u : X}, u∈(chartAt (ComplexModel n) (pi y)).source →
        chartAt (ComplexModel n) (pi y) u∈Phi.source →
        (u∈N ↔ Phi.toFun (chartAt (ComplexModel n) (pi y) u)∈coordSubspace A)) ∧
      (∀ {u : Y}, u∈(chartAt (ComplexModel n) y).source →
        chartAt (ComplexModel n) y u∈Theta.source →
        (u∈geoStrictTransform pi (E.get i∩E.get j) N ↔
          Theta.toFun (chartAt (ComplexModel n) y u)∈coordSubspace A)) ∧
      ∀ a∈A, flatCoord Theta a =ᶠ[𝓝 y] (flatCoord Phi a ∘ pi) := by
  obtain ⟨A,S,⟨Phi0,hsrc0,hzero0,hflat0⟩,hcard⟩ := hTr (pi y) hyN
  let R := S i∪S j
  have hdis : Disjoint R A := Finset.disjoint_union_left.mpr
    ⟨(hcard i hyC.1).2,(hcard j hyC.2).2⟩
  obtain ⟨s,hs⟩ := exists_perm_nested (X:=R) (Y:=R) subset_rfl
  let L := permutationMap s
  let Phi := LocalHolomorphicEquivAt.comp Phi0
    (linearCoordinatesAt (Phi0.toFun (chartAt (ComplexModel n) (pi y) (pi y))) L) rfl
  let B := A.map s.toEmbedding
  let c := n-R.card
  have hsrc : Phi.source ⊆ (chartAt (ComplexModel n) (pi y)).target := fun _ h => hsrc0 h.1
  have hnormal : ∀ a∈B,a.val<c := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp ha
    have hbR : b∉R := fun hbR => Finset.disjoint_left.mp hdis hbR hb
    have := (hs b).1
    change (s b).val<n-R.card
    exact Nat.lt_of_not_le fun h => hbR (this.mp h)
  have hflatN : ∀ {u : X}, u∈(chartAt (ComplexModel n) (pi y)).source →
      chartAt (ComplexModel n) (pi y) u∈Phi.source →
      (u∈N ↔ Phi.toFun (chartAt (ComplexModel n) (pi y) u)∈coordSubspace B) := by
    intro u hu huP
    change u∈N ↔ permutationMap s (Phi0.toFun _)∈coordSubspace (A.map s.toEmbedding)
    rw [permutation_subspace]
    exact hflat0 none hyN hu huP.1
  have hflatC : ∀ {u : X}, u∈(chartAt (ComplexModel n) (pi y)).source →
      chartAt (ComplexModel n) (pi y) u∈Phi.source →
      (u∈E.get i∩E.get j ↔ Phi.toFun (chartAt (ComplexModel n) (pi y) u)∈complexCoordinatePlane n c) := by
    intro u hu huP
    have hR : u∈E.get i∩E.get j ↔ Phi0.toFun (chartAt (ComplexModel n) (pi y) u)∈coordSubspace R := by
      rw [show u∈E.get i∩E.get j ↔ u∈E.get i ∧ u∈E.get j from Iff.rfl]
      have hi : u∈E.get i ↔ Phi0.toFun (chartAt (ComplexModel n) (pi y) u)∈coordSubspace (S i) :=
        hflat0 (some i) hyC.1 hu huP.1
      have hj : u∈E.get j ↔ Phi0.toFun (chartAt (ComplexModel n) (pi y) u)∈coordSubspace (S j) :=
        hflat0 (some j) hyC.2 hu huP.1
      rw [hi,hj]
      constructor
      · rintro ⟨hi,hj⟩ a ha
        exact (Finset.mem_union.mp ha).elim (hi a) (hj a)
      · intro h
        exact ⟨fun a ha => h a (Finset.mem_union_left _ ha),
          fun a ha => h a (Finset.mem_union_right _ ha)⟩
    rw [hR]
    change _ ↔ permutationMap s (Phi0.toFun _)∈complexCoordinatePlane n (n-R.card)
    constructor
    · intro h a ha
      obtain ⟨b,rfl⟩ := s.surjective a
      rw [permutation_apply]
      exact h b ((hs b).1.mp ha)
    · intro h a ha
      rw [←permutation_apply s _ a]
      exact h (s a) ((hs a).1.mpr ha)
  obtain ⟨p,hp,O,hO,hyO,W,hWs,hWeq,hleft,_⟩ :=
    exists_monomialLocalInverse hpi hsrc hflatC (mem_flatDomain_self Phi)
  have hpB : p∉B := fun h => (Nat.not_lt_of_ge hp) (hnormal p h)
  have hmatch : ∀ u∈O,∀ a∈B,flatCoord Phi a (pi u)=W u a := by
    intro u hu a ha
    change Phi.toFun (chartAt (ComplexModel n) (pi y) (pi u)) a=W u a
    rw [←(hWeq u hu).2,monomial_apply,if_neg]
    exact fun h => (Nat.not_lt_of_ge h.1) (hnormal a ha)
  have hWy : W y∈coordSubspace B := by
    intro a ha
    rw [←hmatch y hyO a ha]
    exact (hflatN (hWeq y hyO).1.1 (hWeq y hyO).1.2).mp hyN a ha
  have hstrict : ∀ u∈O,u∈geoStrictTransform pi (E.get i∩E.get j) N ↔ W u∈coordSubspace B := by
    intro u hu
    exact (mem_geoStrictTransform_iff_of_chart hpi hsrc hflatC hflatN hp hO hWs hWeq hleft hu).trans
      (and_iff_right hpB)
  have hWmem : ∀ u∈O,W u∈monomialDomain Phi c p := by
    intro u hu
    show monomial c p (W u)∈Phi.target
    rw [(hWeq u hu).2]
    exact Phi.mapsTo_toFun (hWeq u hu).1.2
  obtain ⟨ell,⟨hells,hellpi⟩,_⟩ := existsUnique_monomialLift hpi hsrc hflatC hp
  have hinj := injective_fderiv_of_monomialInverse hO hWs hWmem hells
    (hleft ell hells hellpi) hyO
  obtain ⟨Theta,htgt,hzero,hTheta⟩ := exists_recentred_coords hO hWs hyO hinj
  refine ⟨B,Phi,Theta,hsrc,htgt,hflatN,?_,?_⟩
  · intro u hu huT
    obtain ⟨huO,huEq⟩ := hTheta hu huT
    have huEq' : Theta.toFun (chartAt (ComplexModel n) y u)=W u-W y := huEq
    rw [huEq',hstrict u huO,sub_mem_coordSubspace_iff hWy]
  · intro a ha
    filter_upwards [(isOpen_flatDomain Theta).mem_nhds (mem_flatDomain_self Theta)] with u hu
    obtain ⟨huO,huEq⟩ := hTheta hu.1 hu.2
    have huEq' : Theta.toFun (chartAt (ComplexModel n) y u)=W u-W y := huEq
    change Theta.toFun (chartAt (ComplexModel n) y u) a=flatCoord Phi a (pi u)
    rw [huEq',PiLp.sub_apply,hWy a ha,sub_zero,hmatch u huO a ha]

-- H4: global ordinary equality of whole functional germ ideals.
theorem exceptional_carrier_ideal_pullback
    (N : Set X) (E : List (Set X))
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hTr : IsTransverse n N E) (i j : Fin E.length) (hij : i≠j)
    (pi : Y→X) (hpi : IsBlowupAlong n (E.get i∩E.get j) pi) :
    GermIdeal.pullback (m:=n) pi (vanishingIdeal (n:=n) N)=
      vanishingIdeal (n:=n) (geoStrictTransform pi (E.get i∩E.get j) N) := by
  apply GermIdeal.ext
  funext y g
  apply propext
  constructor
  · intro hg
    obtain ⟨hhol,hvan⟩ := pullback_vanishingIdeal_le hpi.contMDiff.continuous N y g hg
    refine ⟨hhol,?_⟩
    filter_upwards [hvan] with u hu huT
    exact hu (geoStrictTransform_subset_preimage hpi.contMDiff.continuous hN.1 huT)
  · intro hg
    by_cases hyN : pi y∈N
    · by_cases hyC : pi y∈E.get i∩E.get j
      · obtain ⟨A,Phi,Theta,hsrc,htgt,hflatN,hflatT,hmatch⟩ :=
          exists_matching_transverse_normal_coordinates N E hN hE hTr i j hij pi hpi y hyN hyC
        exact mem_vanishingIdeal_le_pullback_of_matching_normal_coordinates hpi.contMDiff rfl
          Phi Theta hsrc htgt A N _ hflatN hflatT hmatch hg
      · apply mem_pullback_vanishingIdeal_of_notMem hpi N hyC
        apply (vanishingIdeal_mem_congr (g:=g) ?_).mp hg
        have hO : IsOpen (pi ⁻¹' (E.get i∩E.get j)ᶜ) :=
          hpi.1.1.isOpen_compl.preimage hpi.contMDiff.continuous
        filter_upwards [hO.mem_nhds hyC] with u hu
        exact mem_geoStrictTransform_iff_of_notMem hpi.contMDiff.continuous hN.1 hu
    · have hone : (vanishingIdeal (n:=n) N).mem (pi y) (fun _ => 1) := by
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [hN.1.isOpen_compl.mem_nhds hyN] with u hu huN
        exact (hu huN).elim
      apply GermIdeal.mem_pullback_iff.mpr
      exact isInSpanAt_of_eq_mul ⟨(fun _ : X => (1:ℂ)),hone,rfl⟩ hg.1 hg.1
        (Eventually.of_forall fun u => by simp)
end
end Hironaka.HironakaG8TransverseCarrierIdeal
