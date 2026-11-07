module

public import BHSV25.BK.Complete
import Mathlib.Data.List.GetD

/-!
# Soundness of the reduction

`BHSV25/BK/README.md`, Section 3. An independent set `S` of one copy gives folded long codes `f_v`
(`BHSV25.BK.fold`) under which every vertex of `S` whose `a` is not `0` accepts; the accepting
vertices are counted through the averaged long codes `g_u` (`BHSV25.BK.avgTable`, of mean `1/2`
by folding), whose subcube averages have small `t`-th moments by It Ain't Over Till It's Over
unless `u` is one of the few vertices with an influential coordinate
(`BHSV25.BK.Prm.sound`).
-/

@[expose] public section

namespace BHSV25.BK

open Finset UniqueGames OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
open scoped BigOperators

/-! ### Folded tables from compatible demands -/

/-- The negation of a point. -/
def negC {R : ℕ} (w : Cube (Fin R)) : Cube (Fin R) := fun i ↦ !w i

theorem negC_negC {R : ℕ} (w : Cube (Fin R)) : negC (negC w) = w := by
  funext i; simp [negC]

/-- The folded table defined by demands `dem v w` ("`f_v(w) = 1`"): `1` on the demanded points,
`0` on their negations, and the first coordinate elsewhere. -/
noncomputable def fold {R : ℕ} (hR : 0 < R) (dem : ℕ → Cube (Fin R) → Prop) (v : ℕ)
    (w : Cube (Fin R)) : Bool := by
  classical
  exact if dem v w then true else if dem v (negC w) then false else w ⟨0, hR⟩

theorem fold_of_dem {R : ℕ} (hR : 0 < R) {dem : ℕ → Cube (Fin R) → Prop} {v : ℕ}
    {w : Cube (Fin R)} (h : dem v w) : fold hR dem v w = true := by
  simp [fold, h]

/-- **The table is folded** when no point is demanded together with its negation. -/
theorem fold_neg {R : ℕ} (hR : 0 < R) {dem : ℕ → Cube (Fin R) → Prop}
    (hdem : ∀ v w, ¬(dem v w ∧ dem v (negC w))) (v : ℕ) (w : Cube (Fin R)) :
    fold hR dem v (negC w) = !fold hR dem v w := by
  unfold fold
  rw [negC_negC]
  by_cases h1 : dem v w
  · have h2 : ¬dem v (negC w) := fun h2 ↦ hdem v w ⟨h1, h2⟩
    simp [h1, h2]
  · by_cases h2 : dem v (negC w)
    · simp [h1, h2]
    · simp [h1, h2, negC]

/-! ### The averaged long code of a folded family -/

theorem bitVal_not (b : Bool) : bitVal (!b) = 1 - bitVal b := by
  cases b <;> simp [bitVal]

theorem permCube_negC {R : ℕ} {π : List ℕ} (hπ : ∀ i : Fin R, π.getD i 0 < R)
    (x : Cube (Fin R)) : permCube π (negC x) = negC (permCube π x) := by
  funext i
  unfold permCube negC
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true (hπ i)), dite_eq_left_of_eq_true (eq_true (hπ i))]

/-- The entries of a valid table are labels. -/
theorem getD_lt_of_valid {R : ℕ} {c : UGConstraint} (hc : c.2.length = R)
    (hlt : ∀ a ∈ c.2, a < R) (i : Fin R) : c.2.getD i 0 < R := by
  have hi : (i : ℕ) < c.2.length := hc ▸ i.2
  rw [List.getD_eq_getElem _ _ hi]
  exact hlt _ (List.getElem_mem hi)

/-- **Folding halves the averaged long code**: `g_u(¬x) = 1 - g_u(x)`. -/
theorem avgTable_negC {m n R : ℕ} {cs : List UGConstraint} (hv : UGValid (m, n, R, cs))
    {f : ℕ → Cube (Fin R) → Bool} (hf : ∀ v w, f v (negC w) = !f v w) {u : ℕ}
    (hne : nbrs cs u ≠ []) (x : Cube (Fin R)) :
    avgTable cs f u (negC x) = 1 - avgTable cs f u x := by
  have hN : ((nbrs cs u).length : ℝ) ≠ 0 := by
    have := List.length_pos_iff.mpr hne
    positivity
  unfold avgTable
  have e : ((nbrs cs u).map fun c ↦ bitVal (f c.1.2 (permCube c.2 (negC x)))) =
      (nbrs cs u).map fun c ↦ 1 - bitVal (f c.1.2 (permCube c.2 x)) := by
    refine List.map_congr_left fun c hc ↦ ?_
    have hc' := hv c (List.mem_filter.mp hc).1
    rw [permCube_negC (getD_lt_of_valid hc'.2.2.1 hc'.2.2.2.2), hf, bitVal_not]
  rw [e, list_sum_one_sub]
  field_simp

theorem expect_avgTable_le {m n R : ℕ} {cs : List UGConstraint} (hv : UGValid (m, n, R, cs))
    {f : ℕ → Cube (Fin R) → Bool} (hf : ∀ v w, f v (negC w) = !f v w) (u : ℕ) :
    (𝔼 x, avgTable cs f u x) ≤ 1 / 2 := by
  by_cases hne : nbrs cs u = []
  · have : ∀ x, avgTable cs f u x = 0 := fun x ↦ by simp [avgTable, hne]
    simp [this]
  have hinv : Function.Involutive (negC (R := R)) := negC_negC
  have h1 : (𝔼 x, avgTable cs f u x) = 𝔼 x, avgTable cs f u (negC x) :=
    (Fintype.expect_equiv hinv.toPerm _ _ fun x ↦ rfl).symm
  have h2 : (𝔼 x, avgTable cs f u x) + (𝔼 x, avgTable cs f u (negC x)) = 1 := by
    rw [← Finset.expect_add_distrib]
    simp only [avgTable_negC hv hf hne, add_sub_cancel, Finset.expect_const univ_nonempty]
  linarith

/-! ### Products of indicators -/

theorem sum_ind_eq_card {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    ∑ u ∈ s, ind (p u) = ((s.filter p).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine sum_congr rfl fun u _ ↦ ?_
  by_cases h : p u
  · simp [h]
  · simp [h]

theorem ind_forall {ι : Type*} [Fintype ι] (Q : ι → Prop) : ind (∀ p, Q p) = ∏ p, ind (Q p) := by
  by_cases h : ∀ p, Q p
  · rw [ind_of h]
    exact (Finset.prod_eq_one fun p _ ↦ ind_of (h p)).symm
  · push Not at h
    obtain ⟨p, hp⟩ := h
    rw [ind_of_not (fun h' ↦ hp (h' p)), Finset.prod_eq_zero (mem_univ p) (ind_of_not hp)]

namespace Prm

variable (P : Prm)

/-- **A vertex whose `a` is not `0` does not clash with itself**, on simple instances: two of its
demands at the same right vertex come from the same constraint. -/
theorem self_noclash {m n : ℕ} {cs : List UGConstraint} (hv : UGValid (m, n, P.R, cs))
    (hs : UGSimple (m, n, P.R, cs)) {L : ℕ} (hlen : ∀ u < m, (nbrs cs u).length = L)
    {v : P.Vtx m L} (ha : ¬∀ j, (v.1.1.1 j : ℕ) = 0) (p q : Fin P.t) :
    P.clash cs (P.rvS v) (P.rvS v) p q = false := by
  by_contra h
  rw [Bool.not_eq_false, clash, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    conAt_rvS, conAt_rvS] at h
  obtain ⟨hw, hall⟩ := h
  obtain ⟨hc, hcu⟩ := mem_nbrs (P.conV_mem hlen v p)
  obtain ⟨hc', hcu'⟩ := mem_nbrs (P.conV_mem hlen v q)
  have heq : P.conV cs v p = P.conV cs v q :=
    List.inj_on_of_nodup_map hs hc hc' (Prod.ext (hcu.trans hcu'.symm) hw)
  apply ha
  intro j
  have hval := hv _ hc
  obtain ⟨hidx, hget, -⟩ := perm_table (R := P.R) hval.2.2.1 hval.2.2.2.1 hval.2.2.2.2 j
  have hgetq : (P.conV cs v q).2.getD ((P.conV cs v p).2.idxOf j.1) 0 = j := heq ▸ hget
  have h1 := hall _ (List.mem_range.mpr hidx)
  rw [P.fixedAt_rvS cs v p _ j hget, P.fixedAt_rvS cs v q _ j hgetq, P.zAt_rvS cs v p _ j hget,
    P.zAt_rvS cs v q _ j hgetq] at h1
  simpa using h1

/-- At most `N / M` vertices have `a = 0`. -/
theorem sum_ind_zero_le {m L : ℕ} (hR : 0 < P.R) (hM : 0 < P.M) :
    ∑ v : P.Vtx m L, ind (∀ j, (v.1.1.1 j : ℕ) = 0) ≤ P.nV m L / P.M := by
  rw [sum_vtx]
  simp only [Finset.sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ a : Fin P.R → Fin P.M, ind (∀ j, (a j : ℕ) = 0) = 1 := by
    rw [Finset.sum_eq_single (fun _ ↦ ⟨0, hM⟩)]
    · exact ind_of fun _ ↦ rfl
    · intro b _ hb
      refine ind_of_not fun h ↦ hb (funext fun j ↦ Fin.ext (h j))
    · exact fun h ↦ absurd (mem_univ _) h
  rw [h1, nV_eq, le_div_iff₀ (by exact_mod_cast hM)]
  have hMR : (P.M : ℝ) ≤ (P.M : ℝ) ^ P.R := by
    have : (1 : ℝ) ≤ P.M := by exact_mod_cast hM
    calc (P.M : ℝ) = (P.M : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (P.M : ℝ) ^ P.R := pow_le_pow_right₀ this hR
  push_cast
  have h0 : (0 : ℝ) ≤ 2 ^ P.R * (L : ℝ) ^ P.t * m := by positivity
  nlinarith

/-- **Soundness** [BHSV25/BK/README.md, Section 3]: on a simple bi-regular instance with
constraints, if the subcube moments of the averaged long codes without influential coordinates
are at most `γ / 8` (It Ain't Over Till It's Over) and at most `γ m / 8` left vertices have an
influential coordinate (decoding, on instances of small value), then one copy of the graph has
no independent set of `γ N` vertices. -/
theorem sound {G : UGInstance} (hG : Good P.R G) (hL : ldeg G.2.2.2 ≠ 0) (hR : 0 < P.R)
    (hM : 0 < P.M) {γ : ℝ} (hγM : 1 / (P.M : ℝ) ≤ γ / 4) {K : ℕ} {τ : ℝ}
    (hAIO : ∀ g : Cube (Fin P.R) → ℝ, (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (𝔼 x, g x) ≤ 1 / 2 →
      (∀ i, cutoffInfluence K i (fun x ↦ 2 * g x - 1) < τ) →
        (𝔼 z : Cube (Fin P.R), 𝔼 a : Fin P.R → Fin P.M,
          (𝔼 y : Cube (Fin P.R), g (mix a z y)) ^ P.t) ≤ γ / 8)
    (hbad : ∀ f : ℕ → Cube (Fin P.R) → Bool, (((range G.1).filter fun u ↦
        ∃ i, τ ≤ cutoffInfluence K i (fun x ↦ 2 * avgTable G.2.2.2 f u x - 1)).card : ℝ) ≤
          γ / 8 * G.1)
    (S : Finset (Fin (P.nV G.1 (ldeg G.2.2.2))))
    (hS : (P.baseGraph G.2.2.2 G.1 (ldeg G.2.2.2)).2.IsIndepSet (S : Set (Fin _))) :
    (S.card : ℝ) < γ * P.nV G.1 (ldeg G.2.2.2) := by
  classical
  obtain ⟨m, n, R', cs⟩ := G
  obtain ⟨hv, hR', hsimp, hbi⟩ := hG
  dsimp only at hR' hL hbad S hS ⊢
  subst hR'
  have hcs : cs ≠ [] := by
    rintro rfl
    exact hL (by simp [ldeg, nbrs])
  obtain ⟨L, hL0, hm, hlen, -⟩ := exists_leftDeg ⟨hv, rfl, hsimp, hbi⟩ hcs
  have hLD : ldeg cs = L := hlen 0 hm
  revert S
  rw [hLD]
  intro S hS
  set e := P.vEquiv m L
  have hMr : (0 : ℝ) < P.M := by exact_mod_cast hM
  have : Nonempty (Fin P.M) := ⟨⟨0, hM⟩⟩
  have hγ : 0 < γ := by
    have : (0 : ℝ) < 1 / P.M := by positivity
    linarith
  have hN : (0 : ℝ) < P.nV m L := by
    rw [nV_eq]
    have : (0 : ℝ) < L := by exact_mod_cast hL0
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  by_contra hcon
  push Not at hcon
  -- Step 1: the vertices with `a = 0`
  set S' := S.filter fun x ↦ ¬∀ j, ((e x).1.1.1 j : ℕ) = 0 with hS'def
  have hS' : 3 * γ / 4 * P.nV m L ≤ S'.card := by
    have h1 : (S.card : ℝ) ≤ S'.card + ∑ v : P.Vtx m L, ind (∀ j, (v.1.1.1 j : ℕ) = 0) := by
      rw [← e.sum_comp (fun v ↦ ind (∀ j, (v.1.1.1 j : ℕ) = 0)), ← card_filter_eq_sum_ind]
      have := Finset.card_filter_add_card_filter_not
        (s := S) (fun x ↦ ¬∀ j, ((e x).1.1.1 j : ℕ) = 0)
      have h2 : (S.filter fun x ↦ ¬¬∀ j, ((e x).1.1.1 j : ℕ) = 0).card ≤
          (univ.filter fun x ↦ ∀ j, ((e x).1.1.1 j : ℕ) = 0).card := by
        refine Finset.card_le_card fun x hx ↦ ?_
        rw [mem_filter] at hx ⊢
        exact ⟨mem_univ _, not_not.mp hx.2⟩
      have h3 : (S.card : ℝ) = S'.card +
          (S.filter fun x ↦ ¬¬∀ j, ((e x).1.1.1 j : ℕ) = 0).card := by
        rw [hS'def]; exact_mod_cast this.symm
      rw [h3]
      have : ((S.filter fun x ↦ ¬¬∀ j, ((e x).1.1.1 j : ℕ) = 0).card : ℝ) ≤
          (univ.filter fun x ↦ ∀ j, ((e x).1.1.1 j : ℕ) = 0).card := by exact_mod_cast h2
      linarith
    have h4 := P.sum_ind_zero_le (m := m) (L := L) hR hM
    have h5 : (P.nV m L : ℝ) / P.M ≤ γ / 4 * P.nV m L := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hγM hN.le
    linarith
  -- Step 2: the folded long codes
  let dem : ℕ → Cube (Fin P.R) → Prop := fun v' w ↦ ∃ x ∈ S', ∃ p : Fin P.t,
    (P.conV cs (e x) p).1.2 = v' ∧ inSub cs (P.rvS (e x)) p w
  have hdem : ∀ v' w, ¬(dem v' w ∧ dem v' (negC w)) := by
    rintro v' w ⟨⟨x, hx, p, hxv, hxw⟩, ⟨y, hy, q, hyv, hyw⟩⟩
    have hcl : P.clash cs (P.rvS (e x)) (P.rvS (e y)) p q = true := by
      rw [clash_iff, conAt_rvS, conAt_rvS]
      exact ⟨hxv.trans hyv.symm, w, hxw, hyw⟩
    rw [hS'def, mem_filter] at hx hy
    by_cases hxy : x = y
    · subst hxy
      rw [P.self_noclash hv hsimp hlen hx.2 p q] at hcl
      exact Bool.false_ne_true hcl
    · exact hS hx.1 hy.1 hxy ((P.adj_iff cs x y).mpr ⟨hxy, Or.inl ⟨p, q, hcl⟩⟩)
  set f := fold hR dem with hfdef
  have hf : ∀ v w, f v (negC w) = !f v w := fold_neg hR hdem
  -- Step 3: the vertices of `S'` accept
  let A1 : Fin m → Fin L → Cube (Fin P.R) → (Fin P.R → Fin P.M) → Prop := fun u k z a ↦
    ∀ y, f ((nbrs cs u).getD k default).1.2
      (permCube ((nbrs cs u).getD k default).2 (mix a z y)) = true
  have hacc : ∀ x ∈ S', ∀ p, A1 (e x).2 ((e x).1.2 p) (e x).1.1.2 (e x).1.1.1 := by
    intro x hx p y
    refine fold_of_dem hR ⟨x, hx, p, rfl, fun i hfix ↦ ?_⟩
    obtain ⟨hc, -⟩ := mem_nbrs (P.conV_mem hlen (e x) p)
    have hc' := hv _ hc
    have hlt := getD_lt_of_valid hc'.2.2.1 hc'.2.2.2.2 i
    have hj : (P.conV cs (e x) p).2.getD i 0 = (⟨_, hlt⟩ : Fin P.R) := rfl
    rw [P.fixedAt_rvS cs (e x) p i _ hj] at hfix
    rw [P.zAt_rvS cs (e x) p i _ hj]
    have ha : ((e x).1.1.1 ⟨_, hlt⟩ : ℕ) ≠ 0 := by simpa using hfix
    change permCube (P.conV cs (e x) p).2 (mix (e x).1.1.1 (e x).1.1.2 y) i = _
    unfold permCube mix
    rw [dite_eq_left_of_eq_true (eq_true hlt)]
    simp only []
    rw [ite_eq_right_of_eq_false _ _ (eq_false ha)]
  have hS'le : (S'.card : ℝ) ≤
      ∑ v : P.Vtx m L, ind (∀ p, A1 v.2 (v.1.2 p) v.1.1.2 v.1.1.1) := by
    rw [← e.sum_comp (fun v ↦ ind (∀ p, A1 v.2 (v.1.2 p) v.1.1.2 v.1.1.1))]
    calc (S'.card : ℝ) = ∑ x ∈ S', ind (∀ p, A1 (e x).2 ((e x).1.2 p) (e x).1.1.2 (e x).1.1.1) := by
          rw [Finset.sum_congr rfl fun x hx ↦ ind_of (hacc x hx)]
          simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun _ _ _ ↦ ind_nonneg _
  -- Step 4: factorization through the averaged long codes
  set g : Fin m → Cube (Fin P.R) → ℝ := fun u ↦ avgTable cs f u with hg
  have hg01 : ∀ u w, 0 ≤ g u w ∧ g u w ≤ 1 := fun u w ↦ avgTable_mem cs f u w
  have hk : ∀ (u : Fin m) z a, ∑ k : Fin L, ind (A1 u k z a) ≤ L * 𝔼 y, g u (mix a z y) := by
    intro u z a
    have hLr : (L : ℝ) ≠ 0 := by positivity
    have e1 : ∀ y, (L : ℝ) * g u (mix a z y) = ∑ k : Fin L, bitVal
        (f ((nbrs cs u).getD k default).1.2
          (permCube ((nbrs cs u).getD k default).2 (mix a z y))) := by
      intro y
      simp only [hg, avgTable, hlen u u.2]
      rw [list_sum_eq_fin (hlen u u.2)
        (fun c ↦ bitVal (f c.1.2 (permCube c.2 (mix a z y))))]
      field_simp
    rw [Finset.mul_expect, Finset.expect_congr rfl fun y _ ↦ e1 y, Finset.expect_sum_comm]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    by_cases h : A1 u k z a
    · rw [ind_of h, Finset.expect_congr rfl fun y _ ↦ (show bitVal
        (f ((nbrs cs u).getD k default).1.2
          (permCube ((nbrs cs u).getD k default).2 (mix a z y))) = 1 by rw [h y]; rfl)]
      rw [Fintype.expect_const]
    · rw [ind_of_not h]
      exact Finset.expect_nonneg fun y _ ↦ bitVal_nonneg _
  have hfact : ∑ v : P.Vtx m L, ind (∀ p, A1 v.2 (v.1.2 p) v.1.1.2 v.1.1.1) ≤
      (L : ℝ) ^ P.t * ∑ u : Fin m, ∑ z : Cube (Fin P.R), ∑ a : Fin P.R → Fin P.M,
        (𝔼 y, g u (mix a z y)) ^ P.t := by
    rw [sum_vtx]
    simp only [ind_forall]
    have h1 : ∀ (a : Fin P.R → Fin P.M) (z : Cube (Fin P.R)),
        ∑ ks : Fin P.t → Fin L, ∑ u : Fin m, ∏ p, ind (A1 u (ks p) z a) ≤
          (L : ℝ) ^ P.t * ∑ u : Fin m, (𝔼 y, g u (mix a z y)) ^ P.t := by
      intro a z
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_le_sum fun u _ ↦ ?_
      rw [sum_prod_apply (fun k ↦ ind (A1 u k z a)), ← mul_pow]
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ ind_nonneg _) (hk u z a) _
    calc _ ≤ ∑ a : Fin P.R → Fin P.M, ∑ z : Cube (Fin P.R),
          (L : ℝ) ^ P.t * ∑ u : Fin m, (𝔼 y, g u (mix a z y)) ^ P.t :=
          Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun z _ ↦ h1 a z
      _ = (L : ℝ) ^ P.t * ∑ a : Fin P.R → Fin P.M, ∑ z : Cube (Fin P.R),
          ∑ u : Fin m, (𝔼 y, g u (mix a z y)) ^ P.t := by
          simp only [Finset.mul_sum]
      _ = (L : ℝ) ^ P.t * ∑ z : Cube (Fin P.R), ∑ a : Fin P.R → Fin P.M,
          ∑ u : Fin m, (𝔼 y, g u (mix a z y)) ^ P.t := by rw [Finset.sum_comm]
      _ = (L : ℝ) ^ P.t * ∑ z : Cube (Fin P.R), ∑ u : Fin m,
          ∑ a : Fin P.R → Fin P.M, (𝔼 y, g u (mix a z y)) ^ P.t := by
          congr 1
          exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_comm
      _ = _ := by rw [Finset.sum_comm]
  -- Step 5: It Ain't Over Till It's Over and the decoding
  let bad : Fin m → Prop := fun u ↦
    ∃ i, τ ≤ cutoffInfluence K i (fun x ↦ 2 * avgTable cs f u x - 1)
  have hu : ∀ u : Fin m, ∑ z : Cube (Fin P.R), ∑ a : Fin P.R → Fin P.M,
      (𝔼 y, g u (mix a z y)) ^ P.t ≤ 2 ^ P.R * P.M ^ P.R * (γ / 8 + ind (bad u)) := by
    intro u
    have hcz : (Fintype.card (Cube (Fin P.R)) : ℝ) = 2 ^ P.R := by simp
    have hca : (Fintype.card (Fin P.R → Fin P.M) : ℝ) = P.M ^ P.R := by simp
    have hsum_eq : ∑ z : Cube (Fin P.R), ∑ a : Fin P.R → Fin P.M,
        (𝔼 y, g u (mix a z y)) ^ P.t =
          2 ^ P.R * P.M ^ P.R * 𝔼 z : Cube (Fin P.R), 𝔼 a : Fin P.R → Fin P.M,
            (𝔼 y, g u (mix a z y)) ^ P.t := by
      rw [Finset.sum_congr rfl fun z _ ↦ (Fintype.card_mul_expect
        (fun a : Fin P.R → Fin P.M ↦ (𝔼 y, g u (mix a z y)) ^ P.t)).symm, ← Finset.mul_sum,
        ← Fintype.card_mul_expect (fun z : Cube (Fin P.R) ↦ 𝔼 a : Fin P.R → Fin P.M,
          (𝔼 y, g u (mix a z y)) ^ P.t), hcz, hca]
      ring
    have hpos : (0 : ℝ) ≤ 2 ^ P.R * P.M ^ P.R := by positivity
    rw [hsum_eq]
    refine mul_le_mul_of_nonneg_left ?_ hpos
    by_cases hb : bad u
    · rw [ind_of hb]
      have h1 : (𝔼 z : Cube (Fin P.R), 𝔼 a : Fin P.R → Fin P.M,
          (𝔼 y, g u (mix a z y)) ^ P.t) ≤ 1 := by
        refine Finset.expect_le univ_nonempty fun z _ ↦
          Finset.expect_le univ_nonempty fun a _ ↦ ?_
        exact pow_le_one₀ (Finset.expect_nonneg fun y _ ↦ (hg01 u _).1)
          (Finset.expect_le univ_nonempty fun y _ ↦ (hg01 u _).2)
      linarith
    · rw [ind_of_not hb, add_zero]
      refine hAIO (g u) (hg01 u) (expect_avgTable_le hv hf u) ?_
      intro i
      by_contra hi
      exact hb ⟨i, not_lt.mp hi⟩
  have hbadsum : ∑ u : Fin m, ind (bad u) ≤ γ / 8 * m := by
    have e1 : ∑ u : Fin m, ind (bad u) = ∑ u ∈ range m, ind (∃ i,
        τ ≤ cutoffInfluence K i (fun x ↦ 2 * avgTable cs f u x - 1)) :=
      Fin.sum_univ_eq_sum_range (fun u ↦ ind (∃ i,
        τ ≤ cutoffInfluence K i (fun x ↦ 2 * avgTable cs f u x - 1))) m
    rw [e1, sum_ind_eq_card]
    exact hbad f
  have htot : ∑ u : Fin m, ∑ z : Cube (Fin P.R), ∑ a : Fin P.R → Fin P.M,
      (𝔼 y, g u (mix a z y)) ^ P.t ≤ 2 ^ P.R * P.M ^ P.R * (γ / 8 * m + γ / 8 * m) := by
    calc _ ≤ ∑ u : Fin m, 2 ^ P.R * P.M ^ P.R * (γ / 8 + ind (bad u)) := Finset.sum_le_sum
          fun u _ ↦ hu u
      _ = 2 ^ P.R * P.M ^ P.R * (γ / 8 * m + ∑ u : Fin m, ind (bad u)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ _ := by gcongr
  have hNe : (P.nV m L : ℝ) = (L : ℝ) ^ P.t * (2 ^ P.R * P.M ^ P.R * m) := by
    rw [nV_eq]; ring
  have hL' : (0 : ℝ) ≤ (L : ℝ) ^ P.t := by positivity
  have hfin := hS'le.trans (hfact.trans (mul_le_mul_of_nonneg_left htot hL'))
  have : (L : ℝ) ^ P.t * (2 ^ P.R * P.M ^ P.R * (γ / 8 * m + γ / 8 * m)) =
      γ / 4 * P.nV m L := by rw [hNe]; ring
  rw [this] at hfin
  nlinarith

end Prm

end BHSV25.BK
