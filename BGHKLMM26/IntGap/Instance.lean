module

public import BGHKLMM26.IntGap.Cube
public import BGHKLMM26.Hardness.Decoder

/-!
# The Unique Games integrality gap instance

A bipartite form of Khot and Vishnoi's instance [KV15, Section 3], simple and bi-regular as the
reduction of Theorem 1.2 requires (`BGHKLMM26.Hard.GoodI`). With `N = 2^k`:

* **right vertices** are the classes `P ∈ Cls k` of Boolean functions modulo characters, and
  **left vertices** are pairs `u = (Q, Z)` of a class and a set `Z` of `z` points
  (`BGHKLMM26.IntGap.Lft`);
* `u` has one constraint for each function `e` vanishing outside `Z`: to the class
  `P = [rep Q + e]` (`BGHKLMM26.IntGap.tgt`), matching the left label `s` (the function
  `rep Q + χ_s`) with the right label `t` (the function `rep P + χ_t`) when
  `rep Q + χ_s + e = rep P + χ_t`, that is `t = s + κ` with `rep Q + e - rep P = χ_κ`
  (`BGHKLMM26.IntGap.kap`). The table at right label `t` is `t - κ`.

Since two functions vanishing outside `Z` differ by a nonzero character only if `|Z| ≥ N/2`, the
instance is simple when `2z < N` (`BGHKLMM26.IntGap.kvInst_good`); every left vertex has `2^z`
constraints and every right vertex `C(N, z) 2^z`.

Two constraints at the same left vertex `(Q, Z)` match the labels of their classes through the
functions `rep Q + χ_s + e` and `rep Q + χ_s + e'`, which differ only on `Z`: the tuples are
within `1 - 4z/N` (`BGHKLMM26.IntGap.kv_close`).
-/

@[expose] public section

namespace BGHKLMM26.IntGap

open UniqueGames

open scoped RealInnerProductSpace

variable (k z : ℕ)

/-- Left vertices: a class and a set of `z` points. -/
abbrev Lft := Cls k × {Z : Finset (Pt k) // Z.card = z}

/-- The numbering of the left vertices. -/
noncomputable def lIdx : Lft k z ≃ Fin (Fintype.card (Lft k z)) := Fintype.equivFin _

/-- The numbering of the right vertices. -/
noncomputable def rIdx : Cls k ≃ Fin (Fintype.card (Cls k)) := Fintype.equivFin _

theorem card_lab : Fintype.card (Lab k) = 2 ^ k := by
  simp [Lab, ZMod.card]

/-- The numbering of the labels. -/
noncomputable def labIdx : Lab k ≃ Fin (2 ^ k) := Fintype.equivFinOfCardEq (card_lab k)

variable {k z}

/-- `e` vanishes outside `Z`. -/
def Supp (Z : Finset (Pt k)) (e : Fn k) : Prop := ∀ x, x ∉ Z → e x = 0

/-- The class reached from the left vertex `u` by the noise `e`. -/
noncomputable def tgt (u : Lft k z) (e : Fn k) : Cls k := ((rep u.1 + e : Fn k) : Cls k)

/-- The class reached by `e` is the class of `u` translated by the class of `e`. -/
theorem tgt_eq (u : Lft k z) (e : Fn k) : tgt u e = u.1 + (e : Cls k) := by
  rw [tgt, QuotientAddGroup.mk_add,
    show ((rep u.1 : Fn k) : Cls k) = u.1 from QuotientAddGroup.out_eq' _]

theorem exists_kap (u : Lft k z) (e : Fn k) : ∃ s : Lab k, rep u.1 + e - rep (tgt u e) = chi s := by
  obtain ⟨s, hs⟩ := exists_rep_eq (rep u.1 + e)
  refine ⟨-s, ?_⟩
  have h : chi (-s) = -chi s := (chiHom k).map_neg s
  rw [tgt, hs, h]
  abel

/-- The label shift of the constraint: `rep Q + e - rep (tgt u e) = χ_κ`. -/
noncomputable def kap (u : Lft k z) (e : Fn k) : Lab k := Classical.choose (exists_kap u e)

theorem kap_spec (u : Lft k z) (e : Fn k) : rep u.1 + e - rep (tgt u e) = chi (kap u e) :=
  Classical.choose_spec (exists_kap u e)

/-- The label `t` of the class reached by `e` is the function `rep Q + e + χ_{t - κ}`. -/
theorem rep_tgt_add (u : Lft k z) (e : Fn k) (t : Lab k) :
    rep (tgt u e) + chi t = rep u.1 + e + chi (t - kap u e) := by
  have h : chi (t - kap u e) = chi t - chi (kap u e) := (chiHom k).map_sub t (kap u e)
  rw [h, ← kap_spec u e]
  abel

/-- The table of the constraint: at the right label `t`, the left label `t - κ`. -/
noncomputable def table (u : Lft k z) (e : Fn k) : List ℕ :=
  (List.finRange (2 ^ k)).map fun j ↦ (labIdx k ((labIdx k).symm j - kap u e) : ℕ)

/-- The tables are bijections of the labels. -/
theorem table_perm (u : Lft k z) (e : Fn k) :
    (table u e).length = 2 ^ k ∧ (table u e).Nodup ∧ ∀ a ∈ table u e, a < 2 ^ k := by
  refine ⟨by simp [table], (List.nodup_finRange _).map fun i j h ↦ ?_, fun a ha ↦ ?_⟩
  · have h' := (labIdx k).injective (Fin.ext h)
    exact (labIdx k).symm.injective (sub_left_injective h')
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    exact Fin.isLt _

variable (k z) in
open Classical in
/-- The pairs `(u, e)` with `e` vanishing outside the set of `u`. -/
noncomputable def edges : List (Lft k z × Fn k) :=
  (Finset.univ.filter fun p : Lft k z × Fn k ↦ Supp p.1.2.1 p.2).toList

variable (k z) in
/-- **The instance**: `|Lft|` left vertices, `|Cls|` right vertices, `2^k` labels. -/
noncomputable def kvInst : UGInstance :=
  (Fintype.card (Lft k z), Fintype.card (Cls k), 2 ^ k,
    (edges k z).map fun p ↦ (((lIdx k z p.1 : ℕ), (rIdx k (tgt p.1 p.2) : ℕ)), table p.1 p.2))

/-- The pairs listed are those with `e` vanishing outside the set of `u`. -/
theorem mem_edges {p : Lft k z × Fn k} : p ∈ edges k z ↔ Supp p.1.2.1 p.2 := by
  simp [edges]

/-- The constraint of the pair `(u, e)`. -/
noncomputable def kvCon (p : Lft k z × Fn k) : UGConstraint :=
  (((lIdx k z p.1 : ℕ), (rIdx k (tgt p.1 p.2) : ℕ)), table p.1 p.2)

/-- The constraints of the instance. -/
theorem kvInst_cons : (kvInst k z).2.2.2 = (edges k z).map kvCon := rfl

/-- The constraints of the instance are those of the pairs `(u, e)`. -/
theorem mem_kvInst {c : UGConstraint} :
    c ∈ (kvInst k z).2.2.2 ↔ ∃ p : Lft k z × Fn k, Supp p.1.2.1 p.2 ∧ c = kvCon p := by
  rw [kvInst_cons, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, mem_edges.1 hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, mem_edges.2 hp, rfl⟩

/-- Filtering the list of a finset counts the filtered finset. -/
theorem length_filter_toList {α : Type} (s : Finset α) (q : α → Bool) :
    (s.toList.filter q).length = (s.filter fun a ↦ q a).card := by
  rw [Finset.card_def, Finset.filter_val, ← Finset.coe_toList s, Multiset.filter_coe,
    Multiset.coe_card]
  simp

open Classical in
/-- The number of constraints with a property `P` is the number of pairs `(u, e)` with it. -/
theorem length_filter_kvInst (P : UGConstraint → Prop) [DecidablePred P] :
    ((kvInst k z).2.2.2.filter fun c ↦ P c).length =
      (Finset.univ.filter fun p : Lft k z × Fn k ↦ Supp p.1.2.1 p.2 ∧ P (kvCon p)).card := by
  rw [kvInst_cons, List.filter_map, List.length_map, edges, length_filter_toList,
    Finset.filter_filter]
  congr 1

/-- Functions vanishing outside `Z` are the functions on `Z`. -/
theorem card_supp (Z : Finset (Pt k)) [DecidablePred (Supp Z)] :
    (Finset.univ.filter (Supp Z)).card = 2 ^ Z.card := by
  classical
  rw [← Fintype.card_subtype]
  have e : {e : Fn k // Supp Z e} ≃ (Z → ZMod 2) :=
    { toFun e x := e.1 x
      invFun g := ⟨fun x ↦ if h : x ∈ Z then g ⟨x, h⟩ else 0, fun x hx ↦ by simp [hx]⟩
      left_inv e := by
        ext x
        by_cases hx : x ∈ Z
        · simp [hx]
        · simp [hx, e.2 x hx]
      right_inv g := by
        funext x
        simp }
  rw [Fintype.card_congr e]
  simp [ZMod.card]

/-- **Simplicity**: from one left vertex, two noises vanishing outside its set of `z < 2^k / 2`
points reach different classes. -/
theorem eq_of_tgt_eq (hk : 1 ≤ k) (hz : 2 * z < 2 ^ k) {u : Lft k z} {e e' : Fn k}
    (he : Supp u.2.1 e) (he' : Supp u.2.1 e') (h : tgt u e = tgt u e') : e = e' := by
  rw [tgt_eq, tgt_eq] at h
  obtain ⟨s, hs⟩ := (mem_walsh_iff _).1 (QuotientAddGroup.eq.1 (add_left_cancel h))
  by_cases hs0 : s = 0
  · have h0 : chi (0 : Lab k) = 0 := (chiHom k).map_zero
    rw [hs0, h0, neg_add_eq_zero] at hs
    exact hs
  · exfalso
    have hsub : (Finset.univ.filter fun x ↦ chi s x ≠ 0) ⊆ u.2.1 := by
      intro x hx
      by_contra hxZ
      refine (Finset.mem_filter.1 hx).2 ?_
      rw [← hs]
      simp [he x hxZ, he' x hxZ]
    have hle := Finset.card_le_card hsub
    rw [card_chi_ne_zero hs0, u.2.2] at hle
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- **The instance is good**: valid, with `2^k` labels, simple and bi-regular. -/
theorem kvInst_good (hk : 1 ≤ k) (hz : 2 * z < 2 ^ k) : Hard.GoodI (2 ^ k) (kvInst k z) := by
  classical
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨p, -, rfl⟩ := mem_kvInst.1 hc
    exact ⟨(lIdx k z p.1).isLt, (rIdx k _).isLt, table_perm p.1 p.2⟩
  · rw [UGSimple, kvInst_cons, List.map_map]
    refine List.Nodup.map_on (fun p hp q hq hpq ↦ ?_) (Finset.nodup_toList _)
    simp only [Function.comp_apply, kvCon, Prod.mk.injEq] at hpq
    have h1 : p.1 = q.1 := (lIdx k z).injective (Fin.ext hpq.1)
    have h2 : tgt p.1 p.2 = tgt p.1 q.2 := by
      rw [h1]; exact (rIdx k).injective (Fin.ext (h1 ▸ hpq.2))
    have hp' := mem_edges.1 hp
    have hq' := mem_edges.1 hq
    rw [← h1] at hq'
    exact Prod.ext h1 (eq_of_tgt_eq hk hz hp' hq' h2)
  · refine ⟨2 ^ z, fun u hu ↦ ?_⟩
    rw [length_filter_kvInst]
    set w := (lIdx k z).symm ⟨u, hu⟩
    rw [show 2 ^ z = (Finset.univ.filter (Supp w.2.1)).card by rw [card_supp, w.2.2]]
    have hw : ∀ p : Lft k z × Fn k, (kvCon p).1.1 = u → p.1 = w := fun p h ↦
      (Equiv.eq_symm_apply _).2 (Fin.ext h)
    refine Finset.card_nbij' (fun p ↦ p.2) (fun e ↦ (w, e)) (fun p hp ↦ ?_) (fun e he ↦ ?_)
      (fun p hp ↦ ?_) fun e _ ↦ rfl
    · obtain ⟨-, hp1, hp2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw p hp2 ▸ hp1⟩)
    · obtain ⟨-, he⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 he)
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, he, ?_⟩)
      change ((lIdx k z w : Fin _) : ℕ) = u
      simp [w]
    · obtain ⟨-, -, hp2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      exact Prod.ext (hw p hp2).symm rfl
  · refine ⟨(Finset.univ.filter fun q : {Z : Finset (Pt k) // Z.card = z} × Fn k ↦
      Supp q.1.1 q.2).card, fun v hv ↦ ?_⟩
    rw [length_filter_kvInst]
    set P := (rIdx k).symm ⟨v, hv⟩
    have hP : ∀ p : Lft k z × Fn k, (kvCon p).1.2 = v → p.1.1 + (p.2 : Cls k) = P :=
      fun p h ↦ tgt_eq p.1 p.2 ▸ (Equiv.eq_symm_apply _).2 (Fin.ext h)
    refine Finset.card_nbij' (fun p ↦ (p.1.2, p.2)) (fun q ↦ ((P - (q.2 : Cls k), q.1), q.2))
      (fun p hp ↦ ?_) (fun q hq ↦ ?_) (fun p hp ↦ ?_) fun q _ ↦ rfl
    · obtain ⟨-, hp1, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp1⟩)
    · obtain ⟨-, hq⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hq)
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hq, ?_⟩)
      change ((rIdx k (tgt (P - (q.2 : Cls k), q.1) q.2) : Fin _) : ℕ) = v
      rw [tgt_eq, sub_add_cancel]
      simp [P]
    · obtain ⟨-, -, hp2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      refine Prod.ext (Prod.ext ?_ rfl) rfl
      change P - (p.2 : Cls k) = p.1.1
      rw [← hP p hp2, add_sub_cancel_right]

/-- The instance has constraints. -/
theorem kvInst_ne (hz : z ≤ 2 ^ k) : (kvInst k z).2.2.2 ≠ [] := by
  obtain ⟨Z, -, hZ⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Pt k)))
    (n := z) (by simpa [ZMod.card] using hz)
  exact List.ne_nil_of_mem (mem_kvInst.2 ⟨((0, ⟨Z, hZ⟩), 0), fun _ _ ↦ rfl, rfl⟩)

variable (k) in
/-- The class of the right vertex numbered `v`. -/
noncomputable def clsOf (v : ℕ) : Cls k :=
  if h : v < Fintype.card (Cls k) then (rIdx k).symm ⟨v, h⟩ else 0

variable (k) in
/-- The label numbered `j`. -/
noncomputable def labOf (j : ℕ) : Lab k := if h : j < 2 ^ k then (labIdx k).symm ⟨j, h⟩ else 0

/-- `clsOf` inverts the numbering of the right vertices. -/
theorem clsOf_rIdx (P : Cls k) : clsOf k (rIdx k P : ℕ) = P := by
  simp [clsOf]

/-- `labOf` is the inverse numbering of the labels. -/
theorem labOf_eq {j : ℕ} (hj : j < 2 ^ k) : labOf k j = (labIdx k).symm ⟨j, hj⟩ := by
  simp [labOf, hj]

/-- The entry of a table at the right label `j`. -/
theorem table_getD (u : Lft k z) (e : Fn k) {j : ℕ} (hj : j < 2 ^ k) :
    (table u e).getD j 0 = (labIdx k (labOf k j - kap u e) : ℕ) := by
  simp [table, labOf_eq hj, List.getD_eq_getElem?_getD, hj]

/-- **Closeness along two constraints at one left vertex**: right labels matched through the
left label have tuples within `1 - 4z/2^k`. -/
theorem kv_close (hz : 2 * z ≤ 2 ^ k) {c₁ c₂ : UGConstraint} (hc₁ : c₁ ∈ (kvInst k z).2.2.2)
    (hc₂ : c₂ ∈ (kvInst k z).2.2.2) (h12 : c₁.1.1 = c₂.1.1) {j₁ j₂ : ℕ} (hj₁ : j₁ < 2 ^ k)
    (hj₂ : j₂ < 2 ^ k) (hj : c₁.2.getD j₁ 0 = c₂.2.getD j₂ 0) :
    1 - 4 * z / 2 ^ k ≤ ⟪(kvTup k).vec (clsOf k c₁.1.2) (labOf k j₁),
      (kvTup k).vec (clsOf k c₂.1.2) (labOf k j₂)⟫ := by
  obtain ⟨⟨u, e₁⟩, he₁, rfl⟩ := mem_kvInst.1 hc₁
  obtain ⟨⟨u', e₂⟩, he₂, rfl⟩ := mem_kvInst.1 hc₂
  have hu : u = u' := (lIdx k z).injective (Fin.ext h12)
  subst hu
  simp only [kvCon] at hj he₁ he₂ ⊢
  rw [table_getD u e₁ hj₁, table_getD u e₂ hj₂] at hj
  have hs : labOf k j₁ - kap u e₁ = labOf k j₂ - kap u e₂ := (labIdx k).injective (Fin.ext hj)
  rw [clsOf_rIdx, clsOf_rIdx]
  change 1 - 4 * (z : ℝ) / 2 ^ k ≤
    ⟪tvec (rep (tgt u e₁) + chi (labOf k j₁)), tvec (rep (tgt u e₂) + chi (labOf k j₂))⟫
  rw [inner_tvec, rep_tgt_add, rep_tgt_add, hs]
  have hc := corr_ge_of_eqOn (rep u.1 + e₁ + chi (labOf k j₂ - kap u e₂))
    (rep u.1 + e₂ + chi (labOf k j₂ - kap u e₂)) u.2.1 fun x hx ↦ by simp [he₁ x hx, he₂ x hx]
  rw [u.2.2] at hc
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  have ha0 : 0 ≤ 2 * (z : ℝ) / 2 ^ k := by positivity
  have ha1 : 2 * (z : ℝ) / 2 ^ k ≤ 1 := by
    rw [div_le_one hN]; exact_mod_cast hz
  have h4 : 4 * (z : ℝ) / 2 ^ k = 2 * (2 * z / 2 ^ k) := by ring
  rw [h4]
  nlinarith

/-- The tables of two constraints at one left vertex are bijections of the labels. -/
theorem kv_table_perm {c : UGConstraint} (hc : c ∈ (kvInst k z).2.2.2) :
    c.2.length = 2 ^ k ∧ c.2.Nodup ∧ ∀ a ∈ c.2, a < 2 ^ k := by
  obtain ⟨p, -, rfl⟩ := mem_kvInst.1 hc
  exact table_perm p.1 p.2

end BGHKLMM26.IntGap
