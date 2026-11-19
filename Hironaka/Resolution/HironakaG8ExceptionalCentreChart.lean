import Hironaka.Resolution.HironakaG8ExceptionalLogCentre

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Centre charts of an ordinary boundary blowup, and the global ordinary exceptional log equality
(G8 lane, run 0079; leaf G8-3H-C05)

Blueprint: `hironaka-g8-resume-exceptional-centre-chart.tex`.

* `exists_centreChart`: for a closed submanifold `N`, an SNC divisor `E` transverse to `N`, two members
  `E_i, E_j` and the blowup `π` along `C = E_i ∩ E_j`, every point `y` with `π y ∈ C ∩ N` carries a
  `CentreChart` for `(N, E)` and `(strict N, strict E ++ [π⁻¹C])`.  It is built from the transversal chart at
  `π y`, an explicit coordinate permutation, the actual monomial local inverse of the blowup and its
  recentring (the construction of `HironakaG8TransverseCarrierIdeal.exists_matching_transverse_normal_coordinates`,
  extended to every boundary member).
* `exceptional_logIdeal_eq`: the ordinary pullback of the log operator equals the log operator of the
  ordinary exceptional data, globally:
  `π^*(𝓓_{N,E} A) = 𝓓_{N', strict E ++ [π⁻¹C]}(π^*A)` for every ideal `A` of holomorphic germs.  No containment
  `C ⊆ N`, no cosupport, nonzero-ideal, mark or purity hypothesis; `i = j` is allowed.
* `exceptional_logIdeal_iterate_eq`: the same for every iterate.

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ExceptionalCentreChart

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
open Hironaka.BlowupFlatCoordinates Hironaka.NormalCrossings
  Hironaka.SimultaneousNormalCrossings Hironaka.BlowupMonomialCharts
  Hironaka.BlowupLocalSurjectivity Hironaka.BlowupSNCTransform
  Hironaka.BlowupStrictSubmanifold Hironaka.RegularAtDimTransport
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.HironakaG8TransverseCarrierIdeal
  Hironaka.HironakaG8LogDerivEtale
  Hironaka.HironakaG8ExceptionalLogCentre

noncomputable section

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- **Every point over the centre and the carrier carries a centre chart.** -/
theorem exists_centreChart (N : Set X) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hTr : IsTransverse n N E) (i j : Fin E.length) (π : Y → X)
    (hπ : IsBlowupAlong n (E.get i ∩ E.get j) π) {y : Y} (hyN : π y ∈ N)
    (hyC : π y ∈ E.get i ∩ E.get j) :
    Nonempty (CentreChart N E (geoStrictTransform π (E.get i ∩ E.get j) N)
      (E.map (geoStrictTransform π (E.get i ∩ E.get j)) ++ [π ⁻¹' (E.get i ∩ E.get j)]) π y) := by
  classical
  set x := π y with hx
  set C := E.get i ∩ E.get j with hCdef
  obtain ⟨A0, S, ⟨Phi0, hsrc0, hzero0, hflat0⟩, hcard⟩ := hTr x hyN
  set R := S i ∪ S j with hRdef
  have hdis : Disjoint R A0 := Finset.disjoint_union_left.mpr
    ⟨(hcard i hyC.1).2, (hcard j hyC.2).2⟩
  obtain ⟨s, hs⟩ := exists_perm_nested (X := R) (Y := R) subset_rfl
  set L := permutationMap s
  set Phi := LocalHolomorphicEquivAt.comp Phi0
    (linearCoordinatesAt (Phi0.toFun (chartAt (ComplexModel n) x x)) L) rfl with hPhi
  set B := A0.map s.toEmbedding with hB
  set c := n - R.card with hc
  have hsrc : Phi.source ⊆ (chartAt (ComplexModel n) x).target := fun _ h => hsrc0 h.1
  have hPhi_apply : ∀ z, Phi.toFun z = permutationMap s (Phi0.toFun z) := fun _ => rfl
  have hPhi0 : Phi.toFun (chartAt (ComplexModel n) x x) = 0 := by
    rw [hPhi_apply]
    have h0 : Phi0.toFun (chartAt (ComplexModel n) x x) = 0 := hzero0
    rw [h0, map_zero]
  -- boundary indices at `x`
  set bd : Finset (Fin n) :=
    (Finset.univ.filter fun h : Fin E.length => x ∈ E.get h).biUnion fun h => (S h).map s.toEmbedding
    with hbd
  have hsingle : ∀ h : Fin E.length, x ∈ E.get h → ∃ a, S h = {a} := fun h hh =>
    Finset.card_eq_one.mp (hcard h hh).1
  have hflatS : ∀ h : Fin E.length, x ∈ E.get h → ∀ {u : X}, u ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x u ∈ Phi.source →
      (u ∈ E.get h ↔ Phi.toFun (chartAt (ComplexModel n) x u) ∈ coordSubspace ((S h).map s.toEmbedding)) := by
    intro h hh u hu huP
    rw [hPhi_apply, permutation_subspace]
    exact hflat0 (some h) hh hu huP.1
  have hflatN : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x u ∈ Phi.source →
      (u ∈ N ↔ Phi.toFun (chartAt (ComplexModel n) x u) ∈ coordSubspace B) := by
    intro u hu huP
    rw [hPhi_apply, permutation_subspace]
    exact hflat0 none hyN hu huP.1
  have hflatC : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x u ∈ Phi.source →
      (u ∈ C ↔ Phi.toFun (chartAt (ComplexModel n) x u) ∈ complexCoordinatePlane n c) := by
    intro u hu huP
    have hR : u ∈ C ↔ Phi0.toFun (chartAt (ComplexModel n) x u) ∈ coordSubspace R := by
      rw [show u ∈ C ↔ u ∈ E.get i ∧ u ∈ E.get j from Iff.rfl]
      have hi : u ∈ E.get i ↔ Phi0.toFun (chartAt (ComplexModel n) x u) ∈ coordSubspace (S i) :=
        hflat0 (some i) hyC.1 hu huP.1
      have hj : u ∈ E.get j ↔ Phi0.toFun (chartAt (ComplexModel n) x u) ∈ coordSubspace (S j) :=
        hflat0 (some j) hyC.2 hu huP.1
      rw [hi, hj]
      constructor
      · rintro ⟨hi, hj⟩ a ha
        exact (Finset.mem_union.mp ha).elim (hi a) (hj a)
      · intro h
        exact ⟨fun a ha => h a (Finset.mem_union_left _ ha),
          fun a ha => h a (Finset.mem_union_right _ ha)⟩
    rw [hR, hPhi_apply]
    constructor
    · intro h a ha
      obtain ⟨b, rfl⟩ := s.surjective a
      rw [permutation_apply]
      exact h b ((hs b).1.mp ha)
    · intro h a ha
      rw [← permutation_apply s _ a]
      exact h (s a) ((hs a).1.mpr ha)
  -- the high indices are exactly the permuted centre indices, all of them boundary indices
  have hhigh : ∀ l : Fin n, c ≤ l.val → l ∈ bd := by
    intro l hl
    obtain ⟨b, rfl⟩ := s.surjective l
    have hbR : b ∈ R := (hs b).1.mp hl
    rcases Finset.mem_union.mp hbR with hbi | hbj
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyC.1⟩, Finset.mem_map_of_mem _ hbi⟩
    · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyC.2⟩, Finset.mem_map_of_mem _ hbj⟩
  have hBlow : ∀ b ∈ B, b.val < c := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    have haR : a ∉ R := fun haR => Finset.disjoint_left.mp hdis haR ha
    have := (hs a).1
    change (s a).val < n - R.card
    by_contra h
    exact haR (this.mp (Nat.le_of_not_lt h))
  have hdisj : Disjoint bd B := by
    rw [Finset.disjoint_left]
    intro l hl hlB
    obtain ⟨h, hh, hl'⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hl'
    obtain ⟨a', ha', ha'eq⟩ := Finset.mem_map.mp hlB
    have : a' = a := s.injective ha'eq
    subst this
    exact Finset.disjoint_left.mp (hcard h (Finset.mem_filter.mp hh).2).2 ha ha'
  -- the monomial local inverse and the recentred target chart
  obtain ⟨p, hp, O, hO, hyO, W, hWs, hWeq, hleft, -⟩ :=
    exists_monomialLocalInverse hπ hsrc hflatC (mem_flatDomain_self Phi)
  have hWmem : ∀ u ∈ O, W u ∈ monomialDomain Phi c p := by
    intro u hu
    show monomial c p (W u) ∈ Phi.target
    rw [(hWeq u hu).2]
    exact Phi.mapsTo_toFun (hWeq u hu).1.2
  obtain ⟨ell, ⟨hells, hellpi⟩, -⟩ := existsUnique_monomialLift hπ hsrc hflatC hp
  have hinj := injective_fderiv_of_monomialInverse hO hWs hWmem hells (hleft ell hells hellpi) hyO
  obtain ⟨Theta, htgt, hzero, hTheta⟩ := exists_recentred_coords hO hWs hyO hinj
  set v : ComplexModel n := W y with hv
  set Q : Finset (Fin n) := Finset.univ.filter fun l : Fin n => c ≤ l.val ∧ l ≠ p with hQ
  have hmono_y : monomial c p v = 0 := (hWeq y hyO).2.trans hPhi0
  have hv_low : ∀ l : Fin n, l ∉ Q → v l = 0 := by
    intro l hl
    have h := congrArg (fun w : ComplexModel n => w l) hmono_y
    simp only [monomial_apply, PiLp.zero_apply] at h
    have hl' : ¬(c ≤ l.val ∧ l ≠ p) := fun h' => hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
    rwa [if_neg hl'] at h
  have hvp : v p = 0 := hv_low p (by simp [hQ])
  -- target flat coordinates are the recentred inverse coordinates
  have hThetaW : ∀ {u : Y}, u ∈ flatDomain Theta → u ∈ O ∧ ∀ l, flatCoord Theta l u = W u l - v l := by
    intro u hu
    obtain ⟨huO, heq⟩ := hTheta hu.1 hu.2
    refine ⟨huO, fun l => ?_⟩
    have heq' : Theta.toFun (chartAt (ComplexModel n) y u) = W u - v := heq
    change Theta.toFun (chartAt (ComplexModel n) y u) l = W u l - v l
    rw [heq']
    rfl
  have hstrict : ∀ {H : Set X} {T : Finset (Fin n)},
      (∀ {u : X}, u ∈ (chartAt (ComplexModel n) x).source → chartAt (ComplexModel n) x u ∈ Phi.source →
        (u ∈ H ↔ Phi.toFun (chartAt (ComplexModel n) x u) ∈ coordSubspace T)) →
      ∀ u ∈ O, (u ∈ geoStrictTransform π C H ↔ p ∉ T ∧ W u ∈ coordSubspace T) :=
    fun hflatA u hu => mem_geoStrictTransform_iff_of_chart hπ hsrc hflatC hflatA hp hO hWs hWeq hleft hu
  have hExc : ∀ u ∈ O, (π u ∈ C ↔ W u p = 0) := fun u hu => by
    rw [hflatC (hWeq u hu).1.1 (hWeq u hu).1.2, ← (hWeq u hu).2, monomial_mem_plane_iff hp]
  have hOnhds : ∀ᶠ u in 𝓝 y, u ∈ O := hO.mem_nhds hyO
  have hWcont : ContinuousAt W y := (hWs y hyO).continuousAt
  -- a coordinate hyperplane `W_m = 0` with `v_m = 0` is `ζ_m = 0` on the target flat domain
  have hcoordW : ∀ {H' : Set Y} {m : Fin n}, v m = 0 → (∀ u ∈ O, (u ∈ H' ↔ W u m = 0)) →
      ∀ {u : Y}, u ∈ (chartAt (ComplexModel n) y).source → chartAt (ComplexModel n) y u ∈ Theta.source →
        (u ∈ H' ↔ Theta.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace {m}) := by
    intro H' m hvm hH' u hu huT
    obtain ⟨huO, hz⟩ := hThetaW (u := u) ⟨hu, huT⟩
    rw [hH' u huO]
    have hz' := hz m
    change Theta.toFun (chartAt (ComplexModel n) y u) m = W u m - v m at hz'
    rw [show Theta.toFun (chartAt (ComplexModel n) y u) ∈ coordSubspace {m} ↔
      Theta.toFun (chartAt (ComplexModel n) y u) m = 0 by simp [coordSubspace], hz', hvm, sub_zero]
  refine ⟨{
    Φ := Phi
    hΦsrc := hsrc
    Θ := Theta
    hΘsrc := htgt
    Θ_zero := hzero
    B := B
    bd := bd
    p := p
    Q := Q
    v := fun l => v l
    disj := hdisj
    p_bd := hhigh p hp
    Q_bd := fun l hl => hhigh l (Finset.mem_filter.mp hl).2.1
    p_Q := by simp [hQ]
    v_zero := hv_low
    N_flat := hflatN
    E_flat := ?_
    bd_flat := ?_
    mdiff := Eventually.of_forall fun u => (hπ.contMDiff u).mdifferentiableAt (by simp)
    coord_eq := ?_
    N'_flat := ?_
    E'_flat := ?_
    bd'_flat := ?_ }⟩
  · -- `E_flat`
    intro H hH
    obtain ⟨h, rfl⟩ := List.mem_iff_get.mp hH
    by_cases hxh : x ∈ E.get h
    · obtain ⟨a, ha⟩ := hsingle h hxh
      refine Or.inr ⟨s a, Finset.mem_biUnion.mpr ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxh⟩, by simp [ha]⟩, ?_⟩
      intro u hu huP
      have := hflatS h hxh hu huP
      rwa [ha, Finset.map_singleton] at this
    · exact Or.inl ((hE.1 _ (List.get_mem E h)).isOpen_compl.mem_nhds hxh)
  · -- `bd_flat`
    intro m hm
    obtain ⟨h, hh, hm'⟩ := Finset.mem_biUnion.mp hm
    have hxh := (Finset.mem_filter.mp hh).2
    obtain ⟨a, ha⟩ := hsingle h hxh
    rw [ha, Finset.map_singleton, Finset.mem_singleton] at hm'
    subst hm'
    refine ⟨E.get h, List.get_mem E h, fun {u} hu huP => ?_⟩
    have := hflatS h hxh hu huP
    rwa [ha, Finset.map_singleton] at this
  · -- `coord_eq`
    intro l
    filter_upwards [(isOpen_flatDomain Theta).mem_nhds (mem_flatDomain_self Theta)] with u hu
    obtain ⟨huO, hz⟩ := hThetaW hu
    have hmono : flatCoord Phi l (π u) = monomial c p (W u) l := by
      change Phi.toFun (chartAt (ComplexModel n) x (π u)) l = _
      rw [← (hWeq u huO).2]
    simp only [Function.comp_apply, hmono, monomial_apply, hz]
    by_cases hlQ : l ∈ Q
    · have hl : c ≤ l.val ∧ l ≠ p := (Finset.mem_filter.mp hlQ).2
      rw [if_pos hl, if_pos hlQ, hvp]
      ring
    · have hl : ¬(c ≤ l.val ∧ l ≠ p) := fun h' => hlQ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
      rw [if_neg hl, if_neg hlQ, hv_low l hlQ, sub_zero]
  · -- `N'_flat`
    intro u hu huT
    obtain ⟨huO, -⟩ := hThetaW (u := u) ⟨hu, huT⟩
    have hpB : p ∉ B := fun h => (Nat.not_lt.mpr hp) (hBlow p h)
    have hvB : v ∈ coordSubspace B := fun b hb =>
      hv_low b fun hbQ => (Nat.not_lt.mpr (Finset.mem_filter.mp hbQ).2.1) (hBlow b hb)
    obtain ⟨-, heq⟩ := hTheta hu huT
    have heq' : Theta.toFun (chartAt (ComplexModel n) y u) = W u - v := heq
    rw [(hstrict hflatN u huO).trans (and_iff_right hpB), heq']
    exact (sub_mem_coordSubspace_iff hvB).symm
  · -- `E'_flat`
    intro H' hH'
    rcases List.mem_append.mp hH' with hH' | hH'
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      obtain ⟨h, rfl⟩ := List.mem_iff_get.mp hH
      by_cases hxh : x ∈ E.get h
      · obtain ⟨a, ha⟩ := hsingle h hxh
        have hflatH : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) x).source →
            chartAt (ComplexModel n) x u ∈ Phi.source →
            (u ∈ E.get h ↔ Phi.toFun (chartAt (ComplexModel n) x u) ∈ coordSubspace {s a}) := by
          intro u hu huP
          have := hflatS h hxh hu huP
          rwa [ha, Finset.map_singleton] at this
        have hm : s a ∈ bd := Finset.mem_biUnion.mpr ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxh⟩, by simp [ha]⟩
        by_cases hap : s a = p
        · left
          filter_upwards [hOnhds] with u hu hmem
          exact ((hstrict hflatH u hu).mp hmem).1 (by rw [hap]; exact Finset.mem_singleton_self p)
        · by_cases hva : v (s a) = 0
          · right
            refine ⟨s a, hm, hva, hcoordW hva fun u hu => ?_⟩
            rw [hstrict hflatH u hu, and_iff_right (by simpa [eq_comm] using hap)]
            simp [coordSubspace]
          · left
            have hne : ∀ᶠ u in 𝓝 y, W u (s a) ≠ 0 :=
              ((EuclideanSpace.proj (𝕜 := ℂ) (s a)).continuous.continuousAt.comp hWcont).eventually_ne hva
            filter_upwards [hOnhds, hne] with u hu hne' hmem
            exact hne' (((hstrict hflatH u hu).mp hmem).2 (s a) (Finset.mem_singleton_self _))
      · left
        have hcl : IsClosed (E.get h) := hE.1 _ (List.get_mem E h)
        filter_upwards [(hcl.preimage hπ.contMDiff.continuous).isOpen_compl.mem_nhds hxh] with u hu hmem
        exact hu (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hcl hmem)
    · rw [List.mem_singleton] at hH'
      subst hH'
      exact Or.inr ⟨p, hhigh p hp, hvp, hcoordW hvp fun u hu => hExc u hu⟩
  · -- `bd'_flat`
    intro m hm hvm
    by_cases hmp : m = p
    · subst hmp
      exact ⟨π ⁻¹' C, List.mem_append_right _ (List.mem_singleton_self _),
        hcoordW hvm fun u hu => hExc u hu⟩
    · obtain ⟨h, hh, hm'⟩ := Finset.mem_biUnion.mp hm
      have hxh := (Finset.mem_filter.mp hh).2
      obtain ⟨a, ha⟩ := hsingle h hxh
      rw [ha, Finset.map_singleton, Finset.mem_singleton] at hm'
      subst hm'
      have hflatH : ∀ {u : X}, u ∈ (chartAt (ComplexModel n) x).source →
          chartAt (ComplexModel n) x u ∈ Phi.source →
          (u ∈ E.get h ↔ Phi.toFun (chartAt (ComplexModel n) x u) ∈ coordSubspace {s a}) := by
        intro u hu huP
        have := hflatS h hxh hu huP
        rwa [ha, Finset.map_singleton] at this
      refine ⟨geoStrictTransform π C (E.get h),
        List.mem_append_left _ (List.mem_map.mpr ⟨E.get h, List.get_mem E h, rfl⟩),
        hcoordW hvm fun u hu => ?_⟩
      rw [hstrict hflatH u hu, and_iff_right (by simpa [eq_comm] using hmp)]
      simp [coordSubspace]

/-- **C05: the ordinary exceptional log equality, globally.**  For the blowup `π` along the intersection of two
members of an SNC divisor `E` transverse to a closed submanifold `N`, and every ideal `A` of holomorphic germs,
`π^*(𝓓_{N,E} A) = 𝓓_{N', strict E ++ [π⁻¹C]}(π^*A)` with `N'` the strict transform of `N`. -/
theorem exceptional_logIdeal_eq (A : GermIdeal n X) (hA : ∀ x g, A.mem x g → HolomorphicAt n g x)
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hTr : IsTransverse n N E) (i j : Fin E.length) (π : Y → X)
    (hπ : IsBlowupAlong n (E.get i ∩ E.get j) π) :
    GermIdeal.pullback (m := n) π (logDerivIdealAlong N E A) =
      logDerivIdealAlong (geoStrictTransform π (E.get i ∩ E.get j) N)
        (E.map (geoStrictTransform π (E.get i ∩ E.get j)) ++ [π ⁻¹' (E.get i ∩ E.get j)])
        (GermIdeal.pullback (m := n) π A) := by
  apply GermIdeal.ext
  funext y g
  apply propext
  by_cases hy : π y ∈ (E.get i ∩ E.get j) ∩ N
  · obtain ⟨K⟩ := exists_centreChart N E hE hTr i j π hπ hy.2 hy.1
    exact K.log_mem_iff hA g
  · exact blowup_logDerivIdealAlong_mem_iff_of_notMem hπ hN.1 hE.1 hA hy g

/-- **C05, iterated**: the same equality for every iterate of the log operator. -/
theorem exceptional_logIdeal_iterate_eq (A : GermIdeal n X) (hA : ∀ x g, A.mem x g → HolomorphicAt n g x)
    (N : Set X) (E : List (Set X)) (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hTr : IsTransverse n N E) (i j : Fin E.length) (π : Y → X)
    (hπ : IsBlowupAlong n (E.get i ∩ E.get j) π) (r : ℕ) :
    GermIdeal.pullback (m := n) π ((logDerivIdealAlong N E)^[r] A) =
      (logDerivIdealAlong (geoStrictTransform π (E.get i ∩ E.get j) N)
        (E.map (geoStrictTransform π (E.get i ∩ E.get j)) ++ [π ⁻¹' (E.get i ∩ E.get j)]))^[r]
        (GermIdeal.pullback (m := n) π A) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [Function.iterate_succ_apply']
    have hhol : ∀ x g, ((logDerivIdealAlong N E)^[r] A).mem x g → HolomorphicAt n g x := by
      intro x g hg
      cases r with
      | zero => exact hA x g hg
      | succ r =>
        rw [Function.iterate_succ_apply'] at hg
        exact hg.1
    rw [exceptional_logIdeal_eq _ hhol N E hN hE hTr i j π hπ, ih]

end

end Hironaka.HironakaG8ExceptionalCentreChart
