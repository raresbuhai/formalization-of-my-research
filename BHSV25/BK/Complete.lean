module

public import BHSV25.BK.Vertices
public import BHSV25.BK.Copies
import Mathlib.Data.List.GetD

/-!
# Completeness of the reduction

From a labeling `(σ, τ)` satisfying a `1 - δ` fraction of the constraints of a simple bi-regular
instance (`BHSV25/BK/README.md`, Section 2): a vertex `(u, k, z, a)` is *accepted* when its `t`
constraints are satisfied and `σ(u)` is not free; the accepted vertices with `z_{σ(u)} = b` form
an independent set `I_b`, since two demands at a right vertex `v` agree at the coordinate `τ(v)`
(`BHSV25.BK.Prm.no_clash`). Flipping `z_{σ(u)}` exchanges `I_0` and `I_1`, and at most a
`t δ + 1/M` fraction of the vertices is not accepted, so each has at least
`(1 - t δ - 1/M) N / 2` vertices (`BHSV25.BK.Prm.complete`).
-/

@[expose] public section

namespace BHSV25.BK

open Finset UniqueGames OAI.MaxCutGames.Foundations.Hastad

theorem card_filter_eq_sum_ind {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℝ) = ∑ x, ind (p x) := by
  rw [Finset.card_filter]
  push_cast
  refine sum_congr rfl fun x _ ↦ ?_
  by_cases h : p x
  · simp [h]
  · simp [h]

theorem ind_not (p : Prop) : ind (¬p) = 1 - ind p := by
  by_cases h : p
  · rw [ind_of h, ind_of_not (not_not.mpr h)]; norm_num
  · rw [ind_of_not h, ind_of h]; norm_num

theorem ind_and_add (p q : Prop) : ind (p ∧ q) + ind (p ∧ ¬q) = ind p := by
  by_cases hp : p <;> by_cases hq : q <;> simp [ind, hp, hq]

/-- A sum over a list of length `L`, as a sum over `Fin L`. -/
theorem list_sum_eq_fin {l : List UGConstraint} {L : ℕ} (hl : l.length = L)
    (φ : UGConstraint → ℝ) : (l.map φ).sum = ∑ k : Fin L, φ (l.getD k default) := by
  subst hl
  rw [← Fin.sum_univ_fun_getElem l φ]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [List.getD_eq_getElem _ _ k.2]

theorem list_sum_one_sub {α : Type*} (l : List α) (φ : α → ℝ) :
    (l.map fun a ↦ 1 - φ a).sum = l.length - (l.map φ).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

namespace Prm

variable (P : Prm)

theorem sum_vtx {m L : ℕ} (φ : P.Vtx m L → ℝ) :
    ∑ v, φ v = ∑ a : Fin P.R → Fin P.M, ∑ z : Cube (Fin P.R), ∑ ks : Fin P.t → Fin L,
      ∑ u : Fin m, φ (((a, z), ks), u) := by
  simp only [Fintype.sum_prod_type]

theorem nV_eq (m L : ℕ) : (P.nV m L : ℝ) = P.M ^ P.R * 2 ^ P.R * L ^ P.t * m := by
  simp [nV]

/-- The `p`-th constraint of a tuple. -/
def conV (cs : List UGConstraint) {m L : ℕ} (v : P.Vtx m L) (p : Fin P.t) : UGConstraint :=
  (nbrs cs v.2).getD (v.1.2 p) default

theorem conAt_rvS (cs : List UGConstraint) {m L : ℕ} (v : P.Vtx m L) (p : Fin P.t) :
    conAt cs (P.rvS v) p = P.conV cs v p := by
  unfold conAt conV
  rw [P.rvS_ks v p]
  rfl

theorem conflict_iff (cs : List UGConstraint) (r r' : RV) :
    P.conflict cs r r' = true ↔ ∃ p q : Fin P.t, P.clash cs r r' p q = true := by
  unfold conflict
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨p, hp, q, hq, h⟩
    exact ⟨⟨p, hp⟩, ⟨q, hq⟩, h⟩
  · rintro ⟨p, q, h⟩
    exact ⟨p, p.2, q, q.2, h⟩

/-- Adjacency in one copy, through the tuples. -/
theorem adj_iff (cs : List UGConstraint) {m L : ℕ} (x y : Fin (P.nV m L)) :
    (P.baseGraph cs m L).2.Adj x y ↔ x ≠ y ∧
      ((∃ p q : Fin P.t, P.clash cs (P.rvS (P.vEquiv m L x)) (P.rvS (P.vEquiv m L y)) p q = true) ∨
        ∃ p q : Fin P.t, P.clash cs (P.rvS (P.vEquiv m L y)) (P.rvS (P.vEquiv m L x)) p q = true) :=
  by simp only [baseGraph, SimpleGraph.fromRel_adj, rv_eq, conflict_iff]

/-- The coordinate read at `i` by the `p`-th demand of a tuple. -/
theorem jAt_rvS (cs : List UGConstraint) {m L : ℕ} (v : P.Vtx m L) (p : Fin P.t) (i : ℕ) :
    jAt cs (P.rvS v) p i = (P.conV cs v p).2.getD i 0 := by
  unfold jAt; rw [conAt_rvS]

theorem fixedAt_rvS (cs : List UGConstraint) {m L : ℕ} (v : P.Vtx m L) (p : Fin P.t) (i : ℕ)
    (j : Fin P.R) (hj : (P.conV cs v p).2.getD i 0 = j) :
    fixedAt cs (P.rvS v) p i = ((v.1.1.1 j : ℕ) != 0) := by
  unfold fixedAt; rw [jAt_rvS, hj, rvS_a]

theorem zAt_rvS (cs : List UGConstraint) {m L : ℕ} (v : P.Vtx m L) (p : Fin P.t) (i : ℕ)
    (j : Fin P.R) (hj : (P.conV cs v p).2.getD i 0 = j) :
    zAt cs (P.rvS v) p i = v.1.1.2 j := by
  unfold zAt; rw [jAt_rvS, hj, rvS_z]

/-- The constraints of a tuple are constraints at its left vertex. -/
theorem conV_mem {cs : List UGConstraint} {m L : ℕ} (hlen : ∀ u < m, (nbrs cs u).length = L)
    (v : P.Vtx m L) (p : Fin P.t) : P.conV cs v p ∈ nbrs cs v.2 := by
  unfold conV
  have h : (v.1.2 p : ℕ) < (nbrs cs v.2).length := by rw [hlen _ v.2.2]; exact (v.1.2 p).2
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem mem_nbrs {cs : List UGConstraint} {u : ℕ} {c : UGConstraint} (h : c ∈ nbrs cs u) :
    c ∈ cs ∧ c.1.1 = u := by
  unfold nbrs at h
  rw [List.mem_filter] at h
  exact ⟨h.1, of_decide_eq_true h.2⟩

section Complete

variable {m n : ℕ} {cs : List UGConstraint} (σ : Fin m → Fin P.R) (τ : Fin n → Fin P.R)

/-- The constraint `c` is satisfied by `(σ, τ)`. -/
def SatC (c : UGConstraint) : Prop := lab σ c.1.1 = c.2.getD (lab τ c.1.2) 0

/-- An **accepted** tuple: its constraints are satisfied and `σ(u)` is not free. -/
def Acc {L : ℕ} (v : P.Vtx m L) : Prop :=
  (∀ p, P.SatC σ τ (P.conV cs v p)) ∧ (v.1.1.1 (σ v.2) : ℕ) ≠ 0

/-- **Two accepted tuples with the same `z_{σ(u)}` do not clash**: at a common right vertex `w`,
both demands fix the coordinate `τ(w)` to `z_{σ(u)}`. -/
theorem no_clash (hv : UGValid (m, n, P.R, cs)) {L : ℕ}
    (hlen : ∀ u < m, (nbrs cs u).length = L) {v v' : P.Vtx m L}
    (hacc : P.Acc (cs := cs) σ τ v) (hacc' : P.Acc (cs := cs) σ τ v')
    (hz : v.1.1.2 (σ v.2) = v'.1.1.2 (σ v'.2)) (p q : Fin P.t) :
    P.clash cs (P.rvS v) (P.rvS v') p q = false := by
  by_contra h
  rw [Bool.not_eq_false, clash, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    conAt_rvS, conAt_rvS] at h
  obtain ⟨hw, hall⟩ := h
  obtain ⟨hc, hcu⟩ := mem_nbrs (P.conV_mem hlen v p)
  obtain ⟨hc', hcu'⟩ := mem_nbrs (P.conV_mem hlen v' q)
  have hn : (P.conV cs v p).1.2 < n := (hv _ hc).2.1
  set i : ℕ := lab τ (P.conV cs v p).1.2 with hi
  have hiR : i < P.R := by rw [hi, lab_of_lt τ hn]; exact (τ _).2
  have hj : (P.conV cs v p).2.getD i 0 = σ v.2 := by
    rw [← hacc.1 p, hcu, lab_of_lt σ v.2.2]
  have hj' : (P.conV cs v' q).2.getD i 0 = σ v'.2 := by
    rw [hi, hw, ← hacc'.1 q, hcu', lab_of_lt σ v'.2.2]
  have h1 := hall i (List.mem_range.mpr hiR)
  rw [P.fixedAt_rvS cs v p i _ hj, P.fixedAt_rvS cs v' q i _ hj', P.zAt_rvS cs v p i _ hj,
    P.zAt_rvS cs v' q i _ hj', hz] at h1
  have e1 : ((v.1.1.1 (σ v.2) : ℕ) != 0) = true := by simpa using hacc.2
  have e2 : ((v'.1.1.1 (σ v'.2) : ℕ) != 0) = true := by simpa using hacc'.2
  rw [e1, e2] at h1
  simp at h1

/-- The tuple with `z_{σ(u)}` flipped. -/
def flipV {L : ℕ} (v : P.Vtx m L) : P.Vtx m L :=
  (((v.1.1.1, Function.update v.1.1.2 (σ v.2) (!v.1.1.2 (σ v.2))), v.1.2), v.2)

theorem flipV_involutive {L : ℕ} : Function.Involutive (P.flipV (L := L) σ) := by
  intro v
  simp only [flipV, Function.update_self, Bool.not_not, Function.update_idem,
    Function.update_eq_self]

theorem card_vtx (m L : ℕ) : (Fintype.card (P.Vtx m L) : ℝ) = P.nV m L := by
  rw [← Fintype.card_congr (P.vEquiv m L), Fintype.card_fin]

theorem sum_ind_fin_zero {M : ℕ} (hM : 0 < M) : ∑ k : Fin M, ind ((k : ℕ) = 0) = 1 := by
  rw [Finset.sum_eq_single ⟨0, hM⟩ (fun b _ hb ↦ ind_of_not fun h ↦ hb (Fin.ext h))
    (fun h ↦ absurd (mem_univ _) h)]
  exact ind_of rfl

/-- **At most a `t δ + 1/M` fraction of the tuples is not accepted.** -/
theorem acc_count (hv : UGValid (m, n, P.R, cs)) {L : ℕ}
    (hlen : ∀ u < m, (nbrs cs u).length = L) (hcsl : cs.length = m * L) (hM : 0 < P.M)
    (hm : 0 < m) {δ : ℝ}
    (hsat : (1 - δ) * cs.length ≤ ugSatisfied (m, n, P.R, cs) (lab σ) (lab τ)) :
    (1 - P.t * δ - 1 / P.M) * P.nV m L ≤ ∑ v : P.Vtx m L, ind (P.Acc (cs := cs) σ τ v) := by
  have hR : 0 < P.R := (σ ⟨0, hm⟩).pos
  have hMr : (0 : ℝ) < P.M := by exact_mod_cast hM
  -- the unsatisfied constraints
  have hunsat : ∑ u : Fin m, ∑ k : Fin L, ind (¬P.SatC σ τ ((nbrs cs u).getD k default)) ≤
      δ * (m * L) := by
    have e1 : ∑ u : Fin m, ∑ k : Fin L, ind (¬P.SatC σ τ ((nbrs cs u).getD k default)) =
        (cs.map fun c ↦ ind (¬P.SatC σ τ c)).sum := by
      rw [sum_nbrs (G := (m, n, P.R, cs)) hv, ← Fin.sum_univ_eq_sum_range]
      exact sum_congr rfl fun u _ ↦
        (list_sum_eq_fin (hlen u u.2) (fun c ↦ ind (¬P.SatC σ τ c))).symm
    have e2 : (cs.map fun c ↦ ind (¬P.SatC σ τ c)).sum =
        cs.length - (ugSatisfied (m, n, P.R, cs) (lab σ) (lab τ) : ℝ) := by
      unfold ugSatisfied
      rw [length_filter_eq]
      simp only [ind_not]
      exact list_sum_one_sub cs _
    rw [e1, e2]
    have : (cs.length : ℝ) = m * L := by rw [hcsl]; push_cast; ring
    rw [this] at hsat ⊢
    linarith
  -- each query
  have hS1 : ∀ p : Fin P.t, ∑ v : P.Vtx m L, ind (¬P.SatC σ τ (P.conV cs v p)) ≤
      δ * P.nV m L := by
    intro p
    have ht : P.t = P.t - 1 + 1 := (Nat.succ_pred_eq_of_pos p.pos).symm
    rw [sum_vtx]
    simp only [conV]
    rw [Finset.sum_const, Finset.sum_const]
    simp only [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun (u : Fin m) _ ↦ sum_pi_apply p
      (fun k : Fin L ↦ ind (¬P.SatC σ τ ((nbrs cs u).getD k default))), ← Finset.mul_sum,
      Fintype.card_fin, nV_eq]
    push_cast
    calc _ ≤ (P.M : ℝ) ^ P.R * (2 ^ P.R * ((L : ℝ) ^ (P.t - 1) * (δ * (m * L)))) := by
          gcongr
      _ = δ * (P.M ^ P.R * 2 ^ P.R * L ^ P.t * m) := by
          rw [ht, pow_succ]; push_cast; ring
  -- the free label
  have hS2 : ∑ v : P.Vtx m L, ind ((v.1.1.1 (σ v.2) : ℕ) = 0) = P.nV m L / P.M := by
    rw [sum_vtx]
    have e : ∀ a : Fin P.R → Fin P.M, ∑ z : Cube (Fin P.R), ∑ ks : Fin P.t → Fin L,
        ∑ u : Fin m, ind ((a (σ u) : ℕ) = 0) =
          2 ^ P.R * (L ^ P.t * ∑ u : Fin m, ind ((a (σ u) : ℕ) = 0)) := by
      intro a
      rw [Finset.sum_const, Finset.sum_const]
      simp only [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
        nsmul_eq_mul]
      push_cast; ring
    simp only [e]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    simp only [sum_pi_apply _ (fun k : Fin P.M ↦ ind ((k : ℕ) = 0)), sum_ind_fin_zero hM,
      Fintype.card_fin, Finset.sum_const, card_univ, nsmul_eq_mul, mul_one, nV_eq]
    have hR1 : P.R = P.R - 1 + 1 := (Nat.succ_pred_eq_of_pos hR).symm
    field_simp
    rw [hR1, pow_succ]
    push_cast
    ring
  -- assembly
  have hpt : ∀ v : P.Vtx m L, ind (¬P.Acc (cs := cs) σ τ v) ≤
      ∑ p, ind (¬P.SatC σ τ (P.conV cs v p)) + ind ((v.1.1.1 (σ v.2) : ℕ) = 0) := by
    intro v
    by_cases hA : P.Acc (cs := cs) σ τ v
    · rw [ind_of_not (not_not.mpr hA)]
      exact add_nonneg (sum_nonneg fun _ _ ↦ ind_nonneg _) (ind_nonneg _)
    · rw [ind_of hA]
      unfold Acc at hA
      rw [not_and_or] at hA
      rcases hA with hA | hA
      · push Not at hA
        obtain ⟨p, hp⟩ := hA
        have : (1 : ℝ) ≤ ∑ p, ind (¬P.SatC σ τ (P.conV cs v p)) := by
          rw [← ind_of hp]
          exact single_le_sum (f := fun p ↦ ind (¬P.SatC σ τ (P.conV cs v p)))
            (fun _ _ ↦ ind_nonneg _) (mem_univ p)
        linarith [ind_nonneg ((v.1.1.1 (σ v.2) : ℕ) = 0)]
      · rw [not_not] at hA
        rw [ind_of hA]
        linarith [sum_nonneg fun p (_ : p ∈ (univ : Finset (Fin P.t))) ↦
          ind_nonneg (¬P.SatC σ τ (P.conV cs v p))]
  have hnot := sum_le_sum fun v (_ : v ∈ (univ : Finset (P.Vtx m L))) ↦ hpt v
  rw [sum_add_distrib, sum_comm, hS2] at hnot
  have hS1' := sum_le_sum fun p (_ : p ∈ (univ : Finset (Fin P.t))) ↦ hS1 p
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hS1'
  have hnotAcc : ∑ v : P.Vtx m L, ind (¬P.Acc (cs := cs) σ τ v) =
      P.nV m L - ∑ v : P.Vtx m L, ind (P.Acc (cs := cs) σ τ v) := by
    simp only [ind_not, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, card_vtx]
  rw [hnotAcc] at hnot
  have hN : (0 : ℝ) ≤ P.nV m L := Nat.cast_nonneg _
  have : P.nV m L / (P.M : ℝ) = 1 / P.M * P.nV m L := by ring
  nlinarith

end Complete

/-- **Completeness** [BHSV25/BK/README.md, Section 2]: on a simple bi-regular instance with
constraints whose value is at least `1 - δ`, one copy of the graph has two disjoint independent
sets of at least `(1 - t δ - 1/M) N / 2` vertices each. -/
theorem complete {G : UGInstance} (hG : Good P.R G) (hL : ldeg G.2.2.2 ≠ 0) (hM : 0 < P.M)
    {δ : ℝ} (hδ : δ < 1) (hval : 1 - δ ≤ ugValue G) :
    ∃ I J : Finset (Fin (P.nV G.1 (ldeg G.2.2.2))), Disjoint I J ∧
      (P.baseGraph G.2.2.2 G.1 (ldeg G.2.2.2)).2.IsIndepSet (I : Set (Fin _)) ∧
      (P.baseGraph G.2.2.2 G.1 (ldeg G.2.2.2)).2.IsIndepSet (J : Set (Fin _)) ∧
      (1 - P.t * δ - 1 / P.M) * P.nV G.1 (ldeg G.2.2.2) / 2 ≤ I.card ∧
      (1 - P.t * δ - 1 / P.M) * P.nV G.1 (ldeg G.2.2.2) / 2 ≤ J.card := by
  classical
  obtain ⟨m, n, R', cs⟩ := G
  obtain ⟨hv, hR, hsimp, hbi⟩ := hG
  dsimp only at hR hL hval ⊢
  subst hR
  have hcs : cs ≠ [] := by
    rintro rfl
    exact hL (by simp [ldeg, nbrs])
  obtain ⟨D, -, hm, hlen, hcard⟩ := exists_leftDeg ⟨hv, rfl, hsimp, hbi⟩ hcs
  have hLD : ldeg cs = D := hlen 0 hm
  rw [hLD]
  have hpos : 0 < ugValue (m, n, P.R, cs) := by linarith
  obtain ⟨σ, τ, hopt⟩ := exists_opt_labeling _ hpos
  have hcsl : (0 : ℝ) < cs.length := by exact_mod_cast List.length_pos_iff.mpr hcs
  have hsat : (1 - δ) * cs.length ≤ ugSatisfied (m, n, P.R, cs) (lab σ) (lab τ) := by
    rw [hopt, le_div_iff₀ hcsl] at hval
    exact hval
  have hcount := P.acc_count σ τ hv hlen hcard hM hm hsat
  set e := P.vEquiv m D
  set I : Bool → Finset (Fin (P.nV m D)) := fun b ↦
    univ.filter fun x ↦ P.Acc (cs := cs) σ τ (e x) ∧ (e x).1.1.2 (σ (e x).2) = b with hI
  have hsum : ∀ b, ((I b).card : ℝ) =
      ∑ v : P.Vtx m D, ind (P.Acc (cs := cs) σ τ v ∧ v.1.1.2 (σ v.2) = b) := by
    intro b
    rw [hI, card_filter_eq_sum_ind]
    exact e.sum_comp (fun v ↦ ind (P.Acc (cs := cs) σ τ v ∧ v.1.1.2 (σ v.2) = b))
  have hflip : ∑ v : P.Vtx m D, ind (P.Acc (cs := cs) σ τ v ∧ v.1.1.2 (σ v.2) = true) =
      ∑ v : P.Vtx m D, ind (P.Acc (cs := cs) σ τ v ∧ v.1.1.2 (σ v.2) = false) := by
    rw [← Equiv.sum_comp ((P.flipV_involutive (L := D) σ).toPerm _)]
    refine sum_congr rfl fun v _ ↦ ?_
    simp only [Function.Involutive.coe_toPerm, flipV, Function.update_self]
    congr 1
    simp only [Bool.not_eq_true']
    rfl
  have hhalf : ∀ b, ((I b).card : ℝ) = (∑ v : P.Vtx m D, ind (P.Acc (cs := cs) σ τ v)) / 2 := by
    have htot : ∑ v : P.Vtx m D, ind (P.Acc (cs := cs) σ τ v ∧ v.1.1.2 (σ v.2) = true) +
        ∑ v : P.Vtx m D, ind (P.Acc (cs := cs) σ τ v ∧ v.1.1.2 (σ v.2) = false) =
          ∑ v : P.Vtx m D, ind (P.Acc (cs := cs) σ τ v) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun v _ ↦ ?_
      have h := ind_and_add (P.Acc (cs := cs) σ τ v) (v.1.1.2 (σ v.2) = true)
      simp only [Bool.not_eq_true] at h
      exact h
    intro b
    rw [hsum b]
    cases b <;> linarith
  have hindep : ∀ b, (P.baseGraph cs m D).2.IsIndepSet (I b : Set (Fin (P.nV m D))) := by
    intro b x hx y hy hxy hadj
    rw [mem_coe, hI, mem_filter] at hx hy
    rw [adj_iff] at hadj
    have hz : (e x).1.1.2 (σ (e x).2) = (e y).1.1.2 (σ (e y).2) := hx.2.2.trans hy.2.2.symm
    rcases hadj.2 with ⟨p, q, hc⟩ | ⟨p, q, hc⟩
    · rw [P.no_clash σ τ hv hlen hx.2.1 hy.2.1 hz] at hc
      exact Bool.false_ne_true hc
    · rw [P.no_clash σ τ hv hlen hy.2.1 hx.2.1 hz.symm] at hc
      exact Bool.false_ne_true hc
  refine ⟨I true, I false, ?_, hindep true, hindep false, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hI, mem_filter] at hx hx'
    exact absurd (hx.2.2.symm.trans hx'.2.2) (by decide)
  · rw [hhalf]; linarith
  · rw [hhalf]; linarith

end Prm

end BHSV25.BK
