module

public import BGHKLMM26.Hardness.KKMO
public import BGHKLMM26.Hardness.LTF
public import BGHKLMM26.Hardness.KKMORobustFourier

/-!
# The right tables are no farther from the LTFs than the smoothed averaged long codes

[BGHKLMM26, Lemma bound-1], for the reduction without noise: by bi-regularity, the average over
the right vertices `v` of `dist(f_v, ℒ)` is the average over the left vertices `u` of the average
over the constraints `(u, v)` at `u`, and each of these is at most `dist(T_u g_u, ℒ)`
(Claim 4.7, Corollary 4.6, Lemma 4.8) (`BGHKLMM26.Hard.KKMORobust.avg_right_le`).
-/

@[expose] public section

namespace BGHKLMM26.Hard.KKMORobust

open UniqueGames

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

/-! ### Sums over lists -/

theorem list_sum_le_sum {α : Type*} (l : List α) {F H : α → ℝ} (h : ∀ a ∈ l, F a ≤ H a) :
    (l.map F).sum ≤ (l.map H).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun b hb ↦ h b (by simp [hb]))

theorem list_sum_map_const {α : Type*} (l : List α) {F : α → ℝ} {a : ℝ}
    (h : ∀ x ∈ l, F x = a) : (l.map F).sum = l.length * a := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h b (by simp), ih fun x hx ↦ h x (by simp [hx])]
    push_cast; ring

/-- A sum over a list, grouped by a key `< n`. -/
theorem list_sum_fiber {α : Type*} (l : List α) (key : α → ℕ) {n : ℕ}
    (hk : ∀ a ∈ l, key a < n) (F : α → ℝ) :
    (l.map F).sum = ∑ v ∈ range n, ((l.filter fun a ↦ key a = v).map F).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih fun b hb ↦ hk b (List.mem_cons_of_mem a hb)]
    have e : ∀ v, ((List.filter (fun b ↦ decide (key b = v)) (a :: l)).map F).sum =
        (if key a = v then F a else 0) + ((l.filter fun b ↦ key b = v).map F).sum := by
      intro v
      rw [List.filter_cons]
      by_cases h : key a = v
      · simp [h]
      · simp [h]
    rw [Finset.sum_congr rfl fun v _ ↦ e v, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ite_eq_left (mem_range.mpr (hk a (List.mem_cons_self ..)))]

/-! ### Lemma bound-1 -/

variable {R : ℕ}

theorem avgTable_mem (cs : List UGConstraint) (f : ℕ → Cube (Fin R) → Bool) (u : ℕ)
    (x : Cube (Fin R)) : 0 ≤ avgTable cs f u x ∧ avgTable cs f u x ≤ 1 := by
  unfold avgTable
  have hb : ∀ b : Bool, 0 ≤ bitVal b ∧ bitVal b ≤ 1 := fun b ↦ by
    cases b <;> simp [bitVal]
  have h0 : 0 ≤ ((nbrs cs u).map fun c ↦ bitVal (f c.1.2 (permCube c.2 x))).sum := by
    have := list_sum_le_sum (nbrs cs u) (F := fun _ ↦ (0 : ℝ))
      (H := fun c ↦ bitVal (f c.1.2 (permCube c.2 x))) fun c _ ↦ (hb _).1
    simpa using this
  have h1 : ((nbrs cs u).map fun c ↦ bitVal (f c.1.2 (permCube c.2 x))).sum ≤
      (nbrs cs u).length := by
    have := list_sum_le_sum (nbrs cs u) (H := fun _ ↦ (1 : ℝ))
      (F := fun c ↦ bitVal (f c.1.2 (permCube c.2 x))) fun c _ ↦ (hb _).2
    rw [list_sum_map_const (nbrs cs u) (F := fun _ ↦ (1 : ℝ)) fun _ _ ↦ rfl, mul_one] at this
    exact this
  refine ⟨div_nonneg h0 (Nat.cast_nonneg _), ?_⟩
  rcases (Nat.cast_nonneg (α := ℝ) (nbrs cs u).length).eq_or_lt with h | h
  · rw [← h, div_zero]; norm_num
  · exact (div_le_one h).mpr h1

theorem ltfDist_le_one {g : Cube (Fin R) → ℝ} (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) : ltfDist g ≤ 1 := by
  refine (ltfDist_le g (isLTF_const R false)).trans ?_
  refine Finset.expect_le Finset.univ_nonempty fun x _ ↦ ?_
  have hb : bitVal false = 0 := by simp [bitVal]
  rw [hb, sub_zero, abs_of_nonneg (hg x).1]
  exact (hg x).2

/-- **[BGHKLMM26, Lemma bound-1] at one left vertex**: the average distance of the tables `f_v`
of the neighbours is at most that of `T_u g_u` (Claim 4.7, Corollary 4.6, Lemma 4.8). -/
theorem nbrs_avg_le {G : UGInstance} (hV : UGValid G) (hR : G.2.2.1 = R)
    (f : ℕ → Cube (Fin R) → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (w : ℕ)
    (hne : nbrs G.2.2.2 w ≠ []) :
    ((nbrs G.2.2.2 w).map fun c ↦ ltfDist (fun x ↦ bitVal (f c.1.2 x))).sum /
        (nbrs G.2.2.2 w).length ≤ ltfDist (noise u (avgTable G.2.2.2 f w)) := by
  set l := nbrs G.2.2.2 w with hl
  have hperm : ∀ c ∈ l, IsPermTable R c.2 := by
    intro c hc
    have hc' : c ∈ G.2.2.2 := List.mem_of_mem_filter hc
    obtain ⟨-, -, h1, h2, h3⟩ := hV c hc'
    rw [hR] at h1 h3
    exact ⟨h1, h2, h3⟩
  set H : UGConstraint → Cube (Fin R) → ℝ := fun c x ↦ bitVal (f c.1.2 (permCube c.2 x)) with hH
  have hHm : ∀ c x, 0 ≤ H c x ∧ H c x ≤ 1 := fun c x ↦ by
    simp only [hH]; cases f c.1.2 (permCube c.2 x) <;> simp [bitVal]
  have e1 : (l.map fun c ↦ ltfDist (fun x ↦ bitVal (f c.1.2 x))).sum =
      (l.map fun c ↦ ltfDist (H c)).sum := by
    congr 1
    refine List.map_congr_left fun c hc ↦ ?_
    exact (ltfDist_comp_permCube (hperm c hc) (fun x ↦ bitVal (f c.1.2 x))).symm
  have e2 : (l.map fun c ↦ ltfDist (H c)).sum ≤ (l.map fun c ↦ ltfDist (noise u (H c))).sum :=
    list_sum_le_sum l fun c _ ↦ ltfDist_le_noise (by linarith) hu1 _
  have e3 := avg_ltfDist_le l hne (fun c ↦ noise u (H c)) fun c x ↦ noise_mem' hu0 hu1 (hHm c) x
  have e4 : noise u (avgTable G.2.2.2 f w) =
      fun x ↦ (l.map fun c ↦ noise u (H c) x).sum / l.length := by
    rw [← noise_list_avg]
    rfl
  rw [e1, e4]
  have hlen : (0 : ℝ) < l.length := by
    rw [Nat.cast_pos]; exact List.length_pos_iff.mpr hne
  exact (div_le_div_of_nonneg_right e2 hlen.le).trans e3

/-- **[BGHKLMM26, Lemma bound-1]**: by bi-regularity, the average distance of the right tables
`f_v` to the LTFs is at most the average distance of the smoothed averaged long codes `T_u g_u`. -/
theorem avg_right_le {G : UGInstance} (hG : Good R G) (hcs : G.2.2.2 ≠ [])
    (f : ℕ → Cube (Fin R) → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ v ∈ range G.2.1, ltfDist (fun x ↦ bitVal (f v x))) / G.2.1 ≤
      (∑ w ∈ range G.1, ltfDist (noise u (avgTable G.2.2.2 f w))) / G.1 := by
  obtain ⟨hV, hR, -, ⟨DL, hDL⟩, ⟨DR, hDR⟩⟩ := hG
  set cs := G.2.2.2 with hcsdef
  set F : UGConstraint → ℝ := fun c ↦ ltfDist (fun x ↦ bitVal (f c.1.2 x)) with hF
  have hkR : ∀ c ∈ cs, c.1.2 < G.2.1 := fun c hc ↦ (hV c hc).2.1
  have hkL : ∀ c ∈ cs, c.1.1 < G.1 := fun c hc ↦ (hV c hc).1
  -- the right side
  have hRsum : (cs.map F).sum = DR * ∑ v ∈ range G.2.1, ltfDist (fun x ↦ bitVal (f v x)) := by
    rw [list_sum_fiber cs (fun c ↦ c.1.2) hkR F, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv ↦ ?_
    rw [list_sum_map_const _ (a := ltfDist (fun x ↦ bitVal (f v x))) ?_, hDR v (mem_range.mp hv)]
    intro c hc
    have := (List.mem_filter.mp hc).2
    simp only [decide_eq_true_eq] at this
    simp only [hF, this]
  have hRlen : (cs.length : ℝ) = G.2.1 * DR := by
    have := list_sum_fiber cs (fun c ↦ c.1.2) hkR (fun _ ↦ (1 : ℝ))
    rw [list_sum_map_const cs (F := fun _ ↦ (1 : ℝ)) fun _ _ ↦ rfl, mul_one] at this
    rw [this, Finset.sum_congr rfl fun v hv ↦ by
      rw [list_sum_map_const _ (F := fun _ ↦ (1 : ℝ)) fun _ _ ↦ rfl, mul_one,
        hDR v (mem_range.mp hv)]]
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
  -- the left side
  have hLsum : (cs.map F).sum = ∑ w ∈ range G.1, ((nbrs cs w).map F).sum :=
    list_sum_fiber cs (fun c ↦ c.1.1) hkL F
  have hLlen : (cs.length : ℝ) = G.1 * DL := by
    have := list_sum_fiber cs (fun c ↦ c.1.1) hkL (fun _ ↦ (1 : ℝ))
    rw [list_sum_map_const cs (F := fun _ ↦ (1 : ℝ)) fun _ _ ↦ rfl, mul_one] at this
    rw [this, Finset.sum_congr rfl fun w hw ↦ by
      rw [list_sum_map_const _ (F := fun _ ↦ (1 : ℝ)) fun _ _ ↦ rfl, mul_one,
        hDL w (mem_range.mp hw)]]
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
  have hlen0 : (0 : ℝ) < cs.length := by
    rw [Nat.cast_pos]; exact List.length_pos_iff.mpr hcs
  have hn : (0 : ℝ) < G.2.1 := by
    rcases (Nat.cast_nonneg (α := ℝ) G.2.1).eq_or_lt with h | h
    · rw [hRlen, ← h, zero_mul] at hlen0; exact absurd hlen0 (lt_irrefl _)
    · exact h
  have hm : (0 : ℝ) < G.1 := by
    rcases (Nat.cast_nonneg (α := ℝ) G.1).eq_or_lt with h | h
    · rw [hLlen, ← h, zero_mul] at hlen0; exact absurd hlen0 (lt_irrefl _)
    · exact h
  have hDL0 : (0 : ℝ) < DL := by
    rcases (Nat.cast_nonneg (α := ℝ) DL).eq_or_lt with h | h
    · rw [hLlen, ← h, mul_zero] at hlen0; exact absurd hlen0 (lt_irrefl _)
    · exact h
  -- at each left vertex
  have hw : ∀ w ∈ range G.1, ((nbrs cs w).map F).sum ≤
      DL * ltfDist (noise u (avgTable cs f w)) := by
    intro w hw
    have hlen : (nbrs cs w).length = DL := hDL w (mem_range.mp hw)
    have hne : nbrs cs w ≠ [] := by
      intro h
      rw [h, List.length_nil] at hlen
      rw [← hlen, Nat.cast_zero] at hDL0
      exact lt_irrefl _ hDL0
    have := nbrs_avg_le hV hR f hu0 hu1 w hne
    rw [hlen, div_le_iff₀ hDL0] at this
    linarith
  have hsum : DR * ∑ v ∈ range G.2.1, ltfDist (fun x ↦ bitVal (f v x)) ≤
      DL * ∑ w ∈ range G.1, ltfDist (noise u (avgTable cs f w)) := by
    rw [← hRsum, hLsum, Finset.mul_sum]
    exact Finset.sum_le_sum hw
  rw [div_le_div_iff₀ hn hm]
  have hDR0 : (0 : ℝ) < DR := by
    rcases (Nat.cast_nonneg (α := ℝ) DR).eq_or_lt with h | h
    · rw [hRlen, ← h, mul_zero] at hlen0; exact absurd hlen0 (lt_irrefl _)
    · exact h
  have hnm : (G.2.1 : ℝ) * DR = G.1 * DL := by rw [← hRlen, ← hLlen]
  -- `A m DR ≤ B DL m = B n DR`
  have h1 := mul_le_mul_of_nonneg_right hsum hm.le
  refine le_of_mul_le_mul_right (a := (DR : ℝ)) ?_ hDR0
  calc (∑ v ∈ range G.2.1, ltfDist fun x ↦ bitVal (f v x)) * G.1 * DR
      = (DR * ∑ v ∈ range G.2.1, ltfDist fun x ↦ bitVal (f v x)) * G.1 := by ring
    _ ≤ (DL * ∑ w ∈ range G.1, ltfDist (noise u (avgTable cs f w))) * G.1 := h1
    _ = (∑ w ∈ range G.1, ltfDist (noise u (avgTable cs f w))) * (G.1 * DL) := by ring
    _ = (∑ w ∈ range G.1, ltfDist (noise u (avgTable cs f w))) * (G.2.1 * DR) := by rw [hnm]
    _ = _ := by ring

end BGHKLMM26.Hard.KKMORobust
