module

public import BCFGJPSSV26.Greedy.Alg.MergeAux

/-!
# The walk of step B

The walk of step B of the merge (`BCFGJPSSV26.Greedy.Ctx.walkB`, after [CGLSS25, Section 3.5.2])
from a valid sequence `H'p` of regular atoms towards the sequence `Hp` that the greedy algorithm
completes after the prefix:

* every point is a valid sequence after the prefix, with atoms in range and at most one free atom
  (`BCFGJPSSV26.Greedy.Ctx.WPt`);
* consecutive points differ by a free atom appended to a sequence of regular atoms, by a deletion
  followed by a completion with regular atoms, or by a free copy at offset `0` made regular
  (`BCFGJPSSV26.Greedy.Ctx.WTr`);
* each round makes the common prefix with `Hp` longer, so after `L ≥ m + 1` rounds `Hp` is a prefix
  of the last point (`BCFGJPSSV26.Greedy.Ctx.walkB_spec`). The cut `take L` of a deletion never
  acts, since a point has at most `m` regular atoms and one free atom.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

variable {C : Ctx}

theorem delStep_eq (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (Xs Y : List AAtom) (h : AAtom)
    (pts : List (List AAtom × WKind)) :
    C.delStep p f pre Xs.length (Xs ++ h :: Y, pts) =
      ((Xs ++ Y ++ (C.completeSeq (typ1 p) f (C.θseq p) pre.flatten (Xs ++ Y)).drop
          (Xs.length + Y.length)).take C.ip.L,
        pts ++ [((Xs ++ Y ++ (C.completeSeq (typ1 p) f (C.θseq p) pre.flatten (Xs ++ Y)).drop
          (Xs.length + Y.length)).take C.ip.L, .removeComplete Xs h Y
          ((C.completeSeq (typ1 p) f (C.θseq p) pre.flatten (Xs ++ Y)).drop
          (Xs.length + Y.length)))]) := by
  simp [delStep, List.getD_eq_getElem?_getD]

theorem roundB_eq {p : ℕ} {f : ℚ} {pre : List (List AAtom)} {Hp S : List AAtom}
    {pts : List (List AAtom × WKind)} (hnp : ¬ Hp <+: S) {q z : ℕ}
    (hq : commonPrefixLen Hp S = q) (hz : (Hp.getD q (0, 0)).1 = z) :
    C.roundB p f pre Hp (S, pts) =
      (((C.delStep p f pre q)^[S.length - q]
          (S ++ [(z, 1)], pts ++ [(S ++ [(z, 1)], .appendFree z)])).1.set q (z, 0),
        ((C.delStep p f pre q)^[S.length - q]
          (S ++ [(z, 1)], pts ++ [(S ++ [(z, 1)], .appendFree z)])).2 ++
          [(((C.delStep p f pre q)^[S.length - q]
            (S ++ [(z, 1)], pts ++ [(S ++ [(z, 1)], .appendFree z)])).1.set q (z, 0),
            .toRegular)]) := by
  subst hq hz
  simp only [roundB]
  rw [ite_eq_right (by rwa [List.isPrefixOf_iff_prefix])]

theorem roundB_of_prefix {p : ℕ} {f : ℚ} {pre : List (List AAtom)} {Hp : List AAtom}
    {st : List AAtom × List (List AAtom × WKind)} (h : Hp <+: st.1) :
    C.roundB p f pre Hp st = st := by
  simp only [roundB]
  rw [ite_eq_left (List.isPrefixOf_iff_prefix.2 h)]

theorem cpl_of_prefix {l l' : List AAtom} (h : l <+: l') : commonPrefixLen l l' = l.length := by
  exact le_antisymm (cpl_le_left l l') (le_cpl l l' _ le_rfl h.length_le
    (List.take_length.trans (List.prefix_iff_eq_take.1 h)))

/-- A step of the walk, from the sequence `S` to the point `w`. -/
def WTr (S : List AAtom) (w : List AAtom × WKind) : Prop :=
  match w.2 with
  | .init => False
  | .appendFree z => w.1 = S ++ [(z, 1)] ∧ ∀ a ∈ S, a.2 = 0
  | .removeComplete Xs h Y Z => S = Xs ++ h :: Y ∧ w.1 = Xs ++ Y ++ Z ∧ h.2 = 0 ∧
      (∀ a ∈ Z, a.2 = 0) ∧ nFreeSeqA (Xs ++ Y) ≤ 1
  | .toRegular => ∃ A B z, S = A ++ (z, 1) :: B ∧ w.1 = A ++ (z, 0) :: B

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

/-- A point of the walk: a valid sequence after the prefix, with atoms in range and at most one
free atom. -/
def WPt (p b : ℕ) (pre : List (List AAtom)) (W : List AAtom) : Prop :=
  VS hX p b pre W ∧ (∀ a ∈ W, C.AtomOK a) ∧ nFreeSeqA W ≤ 1

/-- The invariant of the list of points of the walk. -/
structure WInv (p b : ℕ) (pre : List (List AAtom)) (H'p : List AAtom)
    (pts : List (List AAtom × WKind)) : Prop where
  head : pts.head? = some (H'p, .init)
  pt : ∀ w ∈ pts, WPt hX p b pre w.1
  tr : ∀ t (ht : t + 1 < pts.length), WTr pts[t].1 pts[t + 1]

variable {p b : ℕ} {pre : List (List AAtom)} {Hp H'p : List AAtom}

theorem WInv.snoc {pts : List (List AAtom × WKind)} (h : WInv hX p b pre H'p pts)
    {S : List AAtom} {κ : WKind} (hlast : pts.getLast? = some (S, κ))
    {w : List AAtom × WKind} (htr : WTr S w) (hw : WPt hX p b pre w.1) :
    WInv hX p b pre H'p (pts ++ [w]) := by
  have hne : pts ≠ [] := by
    rintro rfl
    simp at hlast
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    simpa using h.head
  · intro w' hw'
    rcases List.mem_append.1 hw' with hw' | hw'
    · exact h.pt w' hw'
    · rw [List.mem_singleton.1 hw']
      exact hw
  · intro t ht
    simp only [List.length_append, List.length_singleton] at ht
    by_cases ht' : t + 1 < pts.length
    · rw [List.getElem_append_left ht', List.getElem_append_left (by omega)]
      exact h.tr t ht'
    · have htl : t = pts.length - 1 := by omega
      have hlast' : pts[t]'(by omega) = (S, κ) := by
        rw [List.getLast?_eq_getElem?] at hlast
        subst htl
        exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hlast)
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      simp only [show t + 1 - pts.length = 0 by omega, List.getElem_singleton]
      rw [hlast']
      exact htr

/-! ### The facts about `Hp` -/

section Hp

variable (hlen : pre.length = p) (hokp : C.SolOK pre)
  (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])

include hokp hHp in
theorem Hp_vs : VS hX p b pre Hp := by
  rw [hHp]
  exact vs_completeSeq hX hokp atomsValid_nil (by simp)

include hHp in
theorem Hp_new : ∀ a ∈ Hp, a.2 = 0 ∧ a.1 < C.ip.m := by
  rw [hHp]
  intro a ha
  exact C.completeSeq_new _ _ _ _ [] a (by simpa using ha)

include hHp in
theorem Hp_ok : ∀ a ∈ Hp, C.AtomOK a := fun a ha ↦
  ⟨(Hp_new hHp a ha).2, by rw [(Hp_new hHp a ha).1]; exact Nat.zero_le _⟩

include hX hokp hHp in
theorem Hp_length_le : Hp.length ≤ C.ip.m := by
  have h1 := (Hp_vs hX hokp hHp).nRegSeq_le hX (Hp_ok hHp)
  have h2 := length_eq_nReg_add_nFree Hp
  have h3 := nFreeSeqA_eq_zero fun a ha ↦ (Hp_new hHp a ha).1
  omega

end Hp

/-! ### The deletions of a round -/

/-- A point of the walk has at most `m + 1 ≤ L` atoms. -/
theorem WPt.length_le {W : List AAtom} (h : WPt hX p b pre W) : W.length ≤ C.ip.L := by
  have h1 := h.1.nRegSeq_le hX h.2.1
  have h2 := length_eq_nReg_add_nFree W
  have h3 := hX.L_ge
  have h4 := h.2.2
  omega

theorem dels_spec (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    {z : ℕ} {A : List AAtom} (hAreg : ∀ a ∈ A, a.2 = 0) :
    ∀ (D E : List AAtom) (pts : List (List AAtom × WKind)), (∀ a ∈ D, a.2 = 0) →
      (∀ a ∈ E, a.2 = 0) → WInv hX p b pre H'p pts →
      (∃ κ, pts.getLast? = some (A ++ D ++ (z, 1) :: E, κ)) →
      ∃ E' pts', (C.delStep p (C.fhat b) pre A.length)^[D.length]
          (A ++ D ++ (z, 1) :: E, pts) = (A ++ (z, 1) :: E', pts') ∧
        (∀ a ∈ E', a.2 = 0) ∧ WInv hX p b pre H'p pts' ∧
        ∃ κ, pts'.getLast? = some (A ++ (z, 1) :: E', κ)
  | [], E, pts, _, hE, hinv, hlast => ⟨E, pts, by simp, hE, hinv, by simpa using hlast⟩
  | d :: D, E, pts, hD, hE, hinv, ⟨κ, hlast⟩ => by
    have hd : d.2 = 0 := hD d (by simp)
    have hD' : ∀ a ∈ D, a.2 = 0 := fun a ha ↦ hD a (List.mem_cons_of_mem _ ha)
    rw [List.length_cons, Function.iterate_succ_apply]
    have hcur : A ++ d :: D ++ (z, 1) :: E = A ++ d :: (D ++ (z, 1) :: E) := by simp
    rw [hcur, delStep_eq]
    have hpt : WPt hX p b pre (A ++ d :: (D ++ (z, 1) :: E)) := by
      have := hinv.pt _ (List.mem_of_getLast? hlast)
      rwa [hcur] at this
    have hok1 : ∀ a ∈ A ++ (D ++ (z, 1) :: E), C.AtomOK a := fun a ha ↦ hpt.2.1 a (by
      simp only [List.mem_append, List.mem_cons] at ha ⊢
      tauto)
    -- the facts about the completion
    have hpref := List.prefix_iff_eq_append.1 (C.completeSeq_prefix (typ1 p) (C.fhat b)
      (C.θseq p) pre.flatten (A ++ (D ++ (z, 1) :: E)))
    rw [List.length_append] at hpref
    have hnew := C.completeSeq_new (typ1 p) (C.fhat b) (C.θseq p) pre.flatten
      (A ++ (D ++ (z, 1) :: E))
    rw [List.length_append] at hnew
    have hvsZ : VS hX p b pre (C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten
        (A ++ (D ++ (z, 1) :: E))) := by
      refine vs_completeSeq hX hokp ?_ hok1
      have h1 := hpt.1.1
      rw [show A ++ d :: (D ++ (z, 1) :: E) = A ++ [d] ++ (D ++ (z, 1) :: E) by simp,
        decS_append, decS_append] at h1
      rw [decS_append]
      exact AtomsValid.delete h1
    generalize C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten
      (A ++ (D ++ (z, 1) :: E)) = Zc at hpref hnew hvsZ ⊢
    generalize Zc.drop (A.length + (D ++ (z, 1) :: E).length) = Z at hpref hnew ⊢
    subst hpref
    have hokZ : ∀ a ∈ A ++ (D ++ (z, 1) :: E) ++ Z, C.AtomOK a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hok1 a ha
      · exact ⟨(hnew a ha).2, by rw [(hnew a ha).1]; exact Nat.zero_le _⟩
    have hfreeY : nFreeSeqA (A ++ (D ++ (z, 1) :: E)) = 1 := by
      rw [nFreeSeqA_append, nFreeSeqA_append, nFreeSeqA_cons_free z 0,
        nFreeSeqA_eq_zero hAreg, nFreeSeqA_eq_zero hD', nFreeSeqA_eq_zero hE]
    have hfreeZ : nFreeSeqA (A ++ (D ++ (z, 1) :: E) ++ Z) = 1 := by
      rw [nFreeSeqA_append, hfreeY, nFreeSeqA_eq_zero fun a ha ↦ (hnew a ha).1]
    have hptZ : WPt hX p b pre (A ++ (D ++ (z, 1) :: E) ++ Z) := ⟨hvsZ, hokZ, hfreeZ.le⟩
    rw [List.take_of_length_le (hptZ.length_le hX)]
    have hinv' := hinv.snoc hX hlast (w := (A ++ (D ++ (z, 1) :: E) ++ Z,
      .removeComplete A d (D ++ (z, 1) :: E) Z)) ⟨by rw [hcur], rfl, hd,
        fun a ha ↦ (hnew a ha).1, hfreeY.le⟩ hptZ
    have hZc' : A ++ (D ++ (z, 1) :: E) ++ Z = A ++ D ++ (z, 1) :: (E ++ Z) := by simp
    rw [hZc'] at hinv' ⊢
    exact dels_spec hlen hv hokp hAreg D _ _ hD'
      (fun a ha ↦ by
        rcases List.mem_append.1 ha with ha | ha
        · exact hE a ha
        · exact (hnew a ha).1) hinv' ⟨.removeComplete A d (D ++ (z, 1) :: E) Z, by simp⟩

/-! ### A round -/

/-- **A round of the walk** keeps the invariant and makes the common prefix with `Hp` longer, or
`Hp` is already a prefix. -/
theorem round_spec (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])
    {st : List AAtom × List (List AAtom × WKind)} (hS : ∀ a ∈ st.1, a.2 = 0)
    (hinv : WInv hX p b pre H'p st.2) (hlast : ∃ κ, st.2.getLast? = some (st.1, κ)) :
    (∀ a ∈ (C.roundB p (C.fhat b) pre Hp st).1, a.2 = 0) ∧
      WInv hX p b pre H'p (C.roundB p (C.fhat b) pre Hp st).2 ∧
      (∃ κ, (C.roundB p (C.fhat b) pre Hp st).2.getLast? =
        some ((C.roundB p (C.fhat b) pre Hp st).1, κ)) ∧
      (Hp <+: (C.roundB p (C.fhat b) pre Hp st).1 ∨
        commonPrefixLen Hp st.1 < commonPrefixLen Hp (C.roundB p (C.fhat b) pre Hp st).1) := by
  obtain ⟨S, pts⟩ := st
  simp only at hS hinv hlast ⊢
  by_cases hpre : Hp <+: S
  · rw [roundB_of_prefix hpre]
    exact ⟨hS, hinv, hlast, .inl hpre⟩
  obtain ⟨κ, hlast⟩ := hlast
  have hqHp := cpl_lt_of_not_prefix hpre
  have hqS := cpl_le_right Hp S
  obtain ⟨q, hq⟩ : ∃ q, commonPrefixLen Hp S = q := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, (Hp.getD q (0, 0)).1 = z := ⟨_, rfl⟩
  rw [roundB_eq hpre hq hz]
  rw [hq] at hqHp hqS
  have hHpq : Hp[q] = (z, 0) := by
    rw [← hz, getD_of_lt hqHp]
    exact Prod.ext rfl (Hp_new hHp _ (List.getElem_mem hqHp)).1
  have hzm : z < C.ip.m := by
    have := (Hp_new hHp _ (List.getElem_mem hqHp)).2
    rwa [hHpq] at this
  obtain ⟨A, D, rfl, rfl⟩ : ∃ A D, S = A ++ D ∧ A.length = q :=
    ⟨S.take q, S.drop q, (List.take_append_drop q S).symm, by simp; omega⟩
  have hA : Hp.take A.length = A := by
    have := take_cpl Hp (A ++ D)
    rw [hq] at this
    simpa using this
  have hAreg : ∀ a ∈ A, a.2 = 0 := fun a ha ↦ hS a (List.mem_append_left _ ha)
  have hDreg : ∀ a ∈ D, a.2 = 0 := fun a ha ↦ hS a (List.mem_append_right _ ha)
  rw [show (A ++ D).length - A.length = D.length by simp]
  -- the first point: a free copy of `z` at offset `0`
  have hpt₀ := hinv.pt _ (List.mem_of_getLast? hlast)
  have hpt₁ : WPt hX p b pre (A ++ D ++ [(z, 1)]) := by
    refine ⟨hpt₀.1.append_free hX hlen hv z 0, fun a ha ↦ ?_, ?_⟩
    · rcases List.mem_append.1 ha with ha | ha
      · exact hpt₀.2.1 a ha
      · rw [List.mem_singleton.1 ha]
        exact ⟨hzm, Nat.le_add_left 1 _⟩
    · rw [nFreeSeqA_append, nFreeSeqA_eq_zero hS, nFreeSeqA_free z 0]
  have hinv₁ := hinv.snoc hX hlast (w := (A ++ D ++ [(z, 1)], .appendFree z)) ⟨rfl, hS⟩ hpt₁
  -- the deletions
  obtain ⟨E', pts', hit, hE', hinv', hlast'⟩ := dels_spec hX hlen hv hokp (H'p := H'p) (z := z)
    hAreg D [] _ hDreg (by simp) hinv₁ ⟨.appendFree z, by simp⟩
  rw [hit]
  simp only
  have hset : (A ++ (z, 1) :: E').set A.length (z, 0) = A ++ (z, 0) :: E' := by
    rw [List.set_append_right _ _ le_rfl]
    simp
  rw [hset]
  -- the last point: the free copy made regular
  obtain ⟨κ', hlast'⟩ := hlast'
  have hpt' := hinv'.pt _ (List.mem_of_getLast? hlast')
  have hreg₃ : ∀ a ∈ A ++ (z, 0) :: E', a.2 = 0 := by
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact hAreg a ha
    · rfl
    · exact hE' a ha
  have hpt₃ : WPt hX p b pre (A ++ (z, 0) :: E') := by
    have hv₃ := (Hp_vs hX hokp hHp).1 A.length (by rw [decS_length]; omega)
    have hpairs : pairs (decS hX pre.flatten ++ decS hX (A ++ (z, 0) :: E')) =
        pairs (decS hX pre.flatten ++ decS hX (A ++ (z, 1) :: E')) := by
      rw [decS_append, decS_cons, decS_append, decS_cons, ← List.append_assoc,
        ← List.append_assoc]
      exact pairs_replace (decA_pair_one hX z).symm
    refine ⟨⟨?_, maximal_congr hpt'.1.2 hpairs⟩, fun a ha ↦ ?_, ?_⟩
    · have h1 := hpt'.1.1
      rw [decS_append, decS_cons] at h1 ⊢
      refine AtomsValid.replace h1 (decA_pair_one hX z).symm ?_
      rw [← decS_take, hA] at hv₃
      simp only [decS, List.getElem_map, hHpq] at hv₃
      exact hv₃
    · simp only [List.mem_append, List.mem_cons] at ha
      rcases ha with ha | rfl | ha
      · exact hpt'.2.1 a (by simp [ha])
      · exact ⟨hzm, Nat.zero_le _⟩
      · exact hpt'.2.1 a (by simp [ha])
    · rw [nFreeSeqA_eq_zero hreg₃]
      omega
  have hinv₃ := hinv'.snoc hX hlast' (w := (A ++ (z, 0) :: E', .toRegular))
    ⟨A, E', z, rfl, rfl⟩ hpt₃
  refine ⟨hreg₃, hinv₃, ⟨.toRegular, by simp⟩, .inr ?_⟩
  rw [hq]
  refine Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_cpl _ _ _ (by omega) (by simp) ?_)
  rw [List.take_add_one, List.getElem?_eq_getElem hqHp, hA, hHpq, List.take_append,
    List.take_of_length_le (by omega), show A.length + 1 - A.length = 1 by omega]
  simp

/-! ### The walk -/

theorem rounds_spec (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])
    (hH'p : WPt hX p b pre H'p) (hreg : ∀ a ∈ H'p, a.2 = 0) : ∀ r : ℕ,
    (∀ a ∈ ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).1, a.2 = 0) ∧
      WInv hX p b pre H'p ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).2 ∧
      (∃ κ, ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).2.getLast? =
        some (((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).1, κ)) ∧
      (Hp <+: ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).1 ∨
        r ≤ commonPrefixLen Hp ((C.roundB p (C.fhat b) pre Hp)^[r] (H'p, [(H'p, .init)])).1)
  | 0 => by
    refine ⟨hreg, ⟨rfl, ?_, ?_⟩, ⟨.init, rfl⟩, .inr (Nat.zero_le _)⟩
    · intro w hw
      rw [List.mem_singleton.1 hw]
      exact hH'p
    · intro t ht
      simp at ht
  | r + 1 => by
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2, h3, h4⟩ := rounds_spec hlen hv hokp hHp hH'p hreg r
    obtain ⟨h5, h6, h7, h8⟩ := round_spec hX hlen hv hokp hHp h1 h2 h3
    refine ⟨h5, h6, h7, ?_⟩
    rcases h4 with h4 | h4
    · rw [roundB_of_prefix h4]
      exact .inl h4
    · rcases h8 with h8 | h8
      · exact .inl h8
      · exact .inr (by omega)

/-- **The walk of step B**: its points satisfy the invariant, and it ends with a sequence of
regular atoms with prefix `Hp`. -/
theorem walkB_spec (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])
    (hH'p : VS hX p b pre H'p) (hok : ∀ a ∈ H'p, C.AtomOK a) (hreg : ∀ a ∈ H'p, a.2 = 0) :
    WInv hX p b pre H'p (C.walkB p (C.fhat b) pre Hp H'p) ∧
      ∃ cur κ, (C.walkB p (C.fhat b) pre Hp H'p).getLast? = some (cur, κ) ∧ Hp <+: cur ∧
        ∀ a ∈ cur, a.2 = 0 := by
  have hpt : WPt hX p b pre H'p := ⟨hH'p, hok, by rw [nFreeSeqA_eq_zero hreg]; omega⟩
  obtain ⟨h1, h2, ⟨κ, h3⟩, h4⟩ := rounds_spec hX hlen hv hokp hHp hpt hreg C.ip.L
  refine ⟨h2, _, κ, h3, ?_, h1⟩
  rcases h4 with h4 | h4
  · exact h4
  · have h5 := cpl_le_left Hp ((C.roundB p (C.fhat b) pre Hp)^[C.ip.L] (H'p, [(H'p, .init)])).1
    have h6 := Hp_length_le hX hokp hHp
    have h7 := hX.L_ge
    omega

end BCFGJPSSV26.Greedy.Ctx.MergeH
