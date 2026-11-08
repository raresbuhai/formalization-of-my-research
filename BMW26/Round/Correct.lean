module

public import BMW26.Round.Moments
public import BMW26.Round.Function
public import BMW26.Alg.Program
public import BMW26.SoS.Basic

/-!
# The rounding recovers the hidden vectors

`BMW26.roundOut_recovers`: if the observed graph comes from a subgraph `H` of `Q_d` with about
`p 2^d / 2` edges in each direction, and the moment table is close to `M*` (`BMW26.targetM`) in
squared Frobenius norm, then the rounding (`BMW26.Round.roundOut`) recovers the hidden vectors of
all but `2^d / d^c` vertices, up to an automorphism of `Q_d`.

* For an edge `e = (u, u')` in direction `i`, `h*_e = (d/2)(M*_u - M*_{u'}) = χ̂ᵢ(u) χ̂ᵢ`, and the
  sign vector of `h_e = (d/2)(M_u - M_{u'})` differs from `h*_e` in at most `‖h_e - h*_e‖²`
  positions (`BMW26.Rnd.errE_le`). Summing over the `d 2^(d-1)` edges of `Q_d`,
  `∑_e ‖h_e - h*_e‖² ≤ d³ ‖M - M*‖_F²`, so at most `p 2^d / 64` edges are *bad* (more than
  `T = 2^d / d^(c+2)` errors).
* Each direction has at least `p 2^d / 4` good edges; a good edge is heavy, and a heavy vector is
  within `3T` of a coordinate cut (some good edge is within `2T` of it, since there are fewer bad
  edges than `mth`). Two kept vectors near the same cut are within `6T < n/4`, and vectors near
  different cuts are more than `n/4` apart (`χ̂ᵢ` and `χ̂ⱼ` differ in `n/2` places). So the greedy
  clustering keeps exactly one vector near each cut, in some order `π` (`BMW26.Rnd.greedy_spec`,
  stated for any list of vectors and any centers).
* The errors add up to at most `3 d T ≤ 2^d / d^c` vertices.
-/

@[expose] public section

namespace BMW26

open Finset

namespace Rnd

/-! ### Bit vectors -/

/-- The bits of a list, as a function on `Fin n` (missing bits read as `false`). -/
def bitF (n : ℕ) (a : List Bool) (v : Fin n) : Bool := a.getD v false

/-- The number of positions where two bit functions differ. -/
def fdist {n : ℕ} (f g : Fin n → Bool) : ℕ := #{v | f v ≠ g v}

theorem hamm_eq_fdist (a : List Bool) : ∀ {n : ℕ} (b : List Bool), a.length = n →
    b.length = n → Round.hamm a b = fdist (bitF n a) (bitF n b) := by
  induction a with
  | nil =>
    intro n b ha hb
    subst ha
    have : b = [] := List.length_eq_zero_iff.1 (by simpa using hb)
    subst this
    simp [Round.hamm, fdist]
  | cons x a ih =>
    intro n b ha hb
    cases b with
    | nil => simp at hb; simp at ha; omega
    | cons y b =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨a.length, by simp at ha; omega⟩
      have ih' := ih (n := m) b (by simpa using ha) (by simpa using hb)
      have h1 : Round.hamm (x :: a) (y :: b) =
          Round.hamm a b + if x ≠ y then 1 else 0 := by
        simp only [Round.hamm, List.zipWith_cons_cons, List.count_cons]
        cases x <;> cases y <;> rfl
      rw [h1, ih', fdist, fdist, card_filter, card_filter, Fin.sum_univ_succ, add_comm]
      simp only [bitF, Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
      rfl

theorem fdist_comm {n : ℕ} (f g : Fin n → Bool) : fdist f g = fdist g f := by
  simp only [fdist, ne_comm]

theorem fdist_le {n : ℕ} (f g : Fin n → Bool) : fdist f g ≤ n :=
  (card_filter_le _ _).trans (by simp)

theorem fdist_add_fdist_not {n : ℕ} (f g : Fin n → Bool) :
    fdist f (fun v ↦ !g v) + fdist f g = n := by
  simp only [fdist, card_filter, ← sum_add_distrib]
  calc _ = ∑ _v : Fin n, 1 := sum_congr rfl fun v _ ↦ by cases f v <;> cases g v <;> simp
    _ = n := by simp

theorem fdist_triangle {n : ℕ} (f g h : Fin n → Bool) : fdist f h ≤ fdist f g + fdist g h := by
  simp only [fdist, card_filter, ← sum_add_distrib]
  refine sum_le_sum fun v _ ↦ ?_
  cases f v <;> cases g v <;> cases h v <;> simp

theorem fdist_sum3 {n : ℕ} (f g h : Fin n → Bool) :
    fdist f g + fdist g h + fdist f h ≤ 2 * n := by
  simp only [fdist, card_filter, ← sum_add_distrib]
  calc _ ≤ ∑ _v : Fin n, 2 :=
        sum_le_sum fun v _ ↦ by cases f v <;> cases g v <;> cases h v <;> simp
    _ = 2 * n := by simp [mul_comm]

theorem hamm_self (a : List Bool) : Round.hamm a a = 0 := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    simp only [Round.hamm, List.zipWith_cons_cons, List.count_cons] at ih ⊢
    rw [ih]
    cases x <;> rfl

theorem hammPM_self (n : ℕ) (a : List Bool) : Round.hammPM n a a = 0 := by
  simp [Round.hammPM, hamm_self]

theorem hammPM_eq {n : ℕ} {a b : List Bool} (ha : a.length = n) (hb : b.length = n) :
    Round.hammPM n a b =
      min (fdist (bitF n a) (bitF n b)) (n - fdist (bitF n a) (bitF n b)) := by
  rw [Round.hammPM, hamm_eq_fdist a b ha hb]

theorem hammPM_comm {n : ℕ} {a b : List Bool} (ha : a.length = n) (hb : b.length = n) :
    Round.hammPM n a b = Round.hammPM n b a := by
  rw [hammPM_eq ha hb, hammPM_eq hb ha, fdist_comm]

theorem hammPM_triangle {n : ℕ} {a b c : List Bool} (ha : a.length = n) (hb : b.length = n)
    (hc : c.length = n) : Round.hammPM n a c ≤ Round.hammPM n a b + Round.hammPM n b c := by
  rw [hammPM_eq ha hc, hammPM_eq ha hb, hammPM_eq hb hc]
  have h1 := fdist_triangle (bitF n a) (bitF n b) (bitF n c)
  have h2 := fdist_triangle (bitF n a) (bitF n c) (bitF n b)
  have h3 := fdist_triangle (bitF n b) (bitF n a) (bitF n c)
  have h4 := fdist_sum3 (bitF n a) (bitF n b) (bitF n c)
  have h5 := fdist_le (bitF n a) (bitF n b)
  have h6 := fdist_le (bitF n b) (bitF n c)
  have h7 := fdist_le (bitF n a) (bitF n c)
  rw [fdist_comm (bitF n c) (bitF n b)] at h2
  rw [fdist_comm (bitF n b) (bitF n a)] at h3
  omega

theorem bitF_ofFn {n : ℕ} (g : Fin n → Bool) : bitF n (List.ofFn g) = g := by
  funext v
  simp [bitF, List.getD_eq_getElem?_getD]

/-- The distance up to sign to `g` is at most the distance to `±g`. -/
theorem hammPM_ofFn_le {n : ℕ} {a : List Bool} (ha : a.length = n) (g : Fin n → Bool)
    (t : Bool) : Round.hammPM n a (List.ofFn g) ≤ fdist (bitF n a) (fun v ↦ xor t (g v)) := by
  rw [hammPM_eq ha (by simp), bitF_ofFn]
  cases t
  · simp
  · have := fdist_add_fdist_not (bitF n a) g
    simp only [Bool.true_xor]
    omega

theorem exists_of_hammPM_ofFn_le {n k : ℕ} {a : List Bool} (ha : a.length = n)
    (g : Fin n → Bool) (h : Round.hammPM n a (List.ofFn g) ≤ k) :
    ∃ t : Bool, fdist (bitF n a) (fun v ↦ xor t (g v)) ≤ k := by
  rw [hammPM_eq ha (by simp), bitF_ofFn] at h
  rcases min_le_iff.1 h with h | h
  · exact ⟨false, by simpa using h⟩
  · refine ⟨true, ?_⟩
    have := fdist_add_fdist_not (bitF n a) g
    simp only [Bool.true_xor]
    omega

/-! ### The greedy clustering -/

section Greedy

variable {n T mth : ℕ} {vs : List (List Bool)}

/-- The invariant of the greedy fold: the kept vectors are heavy vectors of `vs`, pairwise more
than `n/4` apart up to sign, and every heavy vector processed so far is within `n/4` of one. -/
theorem greedy_fold (L : List (List Bool)) : ∀ K : List (List Bool), (∀ a ∈ L, a ∈ vs) →
    (∀ b ∈ K, b ∈ vs ∧ Round.heavy n T mth vs b = true) →
    K.Pairwise (fun b b' ↦ n / 4 < Round.hammPM n b' b) →
    (∀ b ∈ L.foldl (Round.greedyStep n T mth vs) K,
        b ∈ vs ∧ Round.heavy n T mth vs b = true) ∧
      (L.foldl (Round.greedyStep n T mth vs) K).Pairwise
        (fun b b' ↦ n / 4 < Round.hammPM n b' b) ∧
      (∀ b ∈ K, b ∈ L.foldl (Round.greedyStep n T mth vs) K) ∧
      ∀ a ∈ L, Round.heavy n T mth vs a = true →
        ∃ b ∈ L.foldl (Round.greedyStep n T mth vs) K, Round.hammPM n a b ≤ n / 4 := by
  induction L with
  | nil =>
    intro K _ hK1 hK2
    exact ⟨hK1, hK2, fun b hb ↦ hb, by simp⟩
  | cons a L ih =>
    intro K hL hK1 hK2
    rw [List.foldl_cons]
    have ha : a ∈ vs := hL a (by simp)
    have hL' : ∀ b ∈ L, b ∈ vs := fun b hb ↦ hL b (by simp [hb])
    by_cases hc : (Round.heavy n T mth vs a &&
        K.all fun b ↦ decide (n / 4 < Round.hammPM n a b)) = true
    · have hK₁ : Round.greedyStep n T mth vs K a = K ++ [a] := by
        rw [Round.greedyStep, ite_eq_left hc]
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      rw [hK₁]
      obtain ⟨h1, h2, h3, h4⟩ := ih (K ++ [a]) hL' (by
        intro b hb
        rcases List.mem_append.1 hb with hb | hb
        · exact hK1 b hb
        · rw [List.mem_singleton.1 hb]; exact ⟨ha, hc.1⟩) (by
        rw [List.pairwise_append]
        exact ⟨hK2, List.pairwise_singleton _ _, fun b hb b' hb' ↦ by
          rw [List.mem_singleton.1 hb']; exact hc.2 b hb⟩)
      refine ⟨h1, h2, fun b hb ↦ h3 b (by simp [hb]), ?_⟩
      intro a' ha' hheavy
      rcases List.mem_cons.1 ha' with rfl | ha'
      · exact ⟨a', h3 a' (by simp), by rw [hammPM_self]; omega⟩
      · exact h4 a' ha' hheavy
    · have hK₁ : Round.greedyStep n T mth vs K a = K := by
        rw [Round.greedyStep, ite_eq_right hc]
      rw [hK₁]
      obtain ⟨h1, h2, h3, h4⟩ := ih K hL' hK1 hK2
      refine ⟨h1, h2, h3, ?_⟩
      intro a' ha' hheavy
      rcases List.mem_cons.1 ha' with rfl | ha'
      · simp only [hheavy, Bool.true_and, List.all_eq_true, decide_eq_true_eq, not_forall,
          not_lt] at hc
        obtain ⟨b, hb, hab⟩ := hc
        exact ⟨b, h3 b hb, hab⟩
      · exact h4 a' ha' hheavy

/-- **The greedy clustering**: if fewer than `mth` vectors are far (more than `T`) from all the
centers `w i`, each center has at least `mth` vectors within `T`, the centers are more than
`n/4 + 6T` apart, and `6T ≤ n/4`, then the greedy clustering keeps exactly one vector near each
center (within `3T`, up to sign). -/
theorem greedy_spec {d : ℕ} (w : Fin d → List Bool)
    (hlen : ∀ a ∈ vs, a.length = n) (hw : ∀ i, (w i).length = n)
    (hsep : ∀ i j, i ≠ j → n / 4 + 6 * T < Round.hammPM n (w i) (w j))
    (hT : 6 * T ≤ n / 4)
    (hbad : vs.countP (fun a ↦ decide (∀ i, T < Round.hammPM n a (w i))) < mth)
    (hgood : ∀ i, mth ≤ vs.countP (fun a ↦ decide (Round.hammPM n a (w i) ≤ T))) :
    (Round.greedy n T mth vs).length = d ∧ ∃ σ : Equiv.Perm (Fin d), ∀ k : Fin d,
      ((Round.greedy n T mth vs).getD k []).length = n ∧
        Round.hammPM n ((Round.greedy n T mth vs).getD k []) (w (σ k)) ≤ 3 * T := by
  -- heavy vectors are near a center
  have hnear : ∀ a, a.length = n → Round.heavy n T mth vs a = true →
      ∃ i, Round.hammPM n a (w i) ≤ 3 * T := by
    intro a ha hh
    have hh' : mth ≤ vs.countP (fun b ↦ decide (Round.hammPM n a b ≤ 2 * T)) := by
      simpa [Round.heavy, List.countP_eq_length_filter] using hh
    by_contra hcon
    push Not at hcon
    have : vs.countP (fun b ↦ decide (Round.hammPM n a b ≤ 2 * T)) ≤
        vs.countP (fun a ↦ decide (∀ i, T < Round.hammPM n a (w i))) := by
      refine List.countP_mono_left fun b hb hab ↦ ?_
      simp only [decide_eq_true_eq] at hab ⊢
      intro i
      by_contra hbi
      push Not at hbi
      have := hammPM_triangle ha (hlen b hb) (hw i)
      have := hcon i
      omega
    omega
  -- every center has a heavy vector near it
  have hcov : ∀ i, ∃ a ∈ vs, Round.heavy n T mth vs a = true ∧ Round.hammPM n a (w i) ≤ T := by
    intro i
    have hpos : 0 < vs.countP (fun a ↦ decide (Round.hammPM n a (w i) ≤ T)) := by
      have := hgood i
      omega
    obtain ⟨a, ha, hai⟩ := List.countP_pos_iff.1 hpos
    simp only [decide_eq_true_eq] at hai
    refine ⟨a, ha, ?_, hai⟩
    simp only [Round.heavy, decide_eq_true_eq, ← List.countP_eq_length_filter]
    refine (hgood i).trans (List.countP_mono_left fun b hb hbi ↦ ?_)
    simp only [decide_eq_true_eq] at hbi ⊢
    have := hammPM_triangle (hlen a ha) (hw i) (hlen b hb)
    rw [hammPM_comm (hw i) (hlen b hb)] at this
    omega
  obtain ⟨hG1, hG2, -, hG4⟩ := greedy_fold (n := n) (T := T) (mth := mth) (vs := vs) vs []
    (fun a ha ↦ ha) (by simp) List.Pairwise.nil
  have hG : Round.greedy n T mth vs = vs.foldl (Round.greedyStep n T mth vs) [] := rfl
  rw [← hG] at hG1 hG2 hG4
  set G := Round.greedy n T mth vs with hGdef
  have hGlen : ∀ k : Fin G.length, G[k].length = n := fun k ↦
    hlen _ (hG1 _ (List.getElem_mem _)).1
  have hc : ∀ k : Fin G.length, ∃ i, Round.hammPM n G[k] (w i) ≤ 3 * T := fun k ↦
    hnear _ (hGlen k) (hG1 _ (List.getElem_mem _)).2
  choose c hc using hc
  have key : ∀ k k' : Fin G.length, k < k' → c k = c k' → False := by
    intro k k' hlt heq
    have hp := List.pairwise_iff_getElem.1 hG2 k k' k.2 k'.2 hlt
    have t1 := hammPM_triangle (hGlen k') (hw (c k)) (hGlen k)
    rw [hammPM_comm (hw (c k)) (hGlen k)] at t1
    have h1 := hc k
    have h2 := hc k'
    rw [← heq] at h2
    simp only [Fin.getElem_fin] at h1 h2 t1
    omega
  have hinj : Function.Injective c := by
    intro k k' hkk'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key k k' h hkk'
    · exact key k' k h hkk'.symm
  have hsurj : Function.Surjective c := by
    intro i
    obtain ⟨a, ha, hheavy, hai⟩ := hcov i
    obtain ⟨b, hb, hab⟩ := hG4 a ha hheavy
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hb
    refine ⟨⟨k, hk⟩, ?_⟩
    by_contra hne
    have h1 := hc ⟨k, hk⟩
    have h2 := hsep i (c ⟨k, hk⟩) (Ne.symm hne)
    have t1 := hammPM_triangle (hw i) (hlen a ha) (hw (c ⟨k, hk⟩))
    have t2 := hammPM_triangle (hlen a ha) (hGlen ⟨k, hk⟩) (hw (c ⟨k, hk⟩))
    rw [hammPM_comm (hw i) (hlen a ha)] at t1
    simp only [Fin.getElem_fin] at h1 t2
    omega
  have hbij : Function.Bijective c := ⟨hinj, hsurj⟩
  have hlenG : G.length = d := by simpa using Fintype.card_of_bijective hbij
  refine ⟨hlenG, (finCongr hlenG.symm).trans (Equiv.ofBijective c hbij), fun k ↦ ?_⟩
  have hk : (k : ℕ) < G.length := by omega
  have h1 := hc (Fin.cast hlenG.symm k)
  have h2 := hGlen (Fin.cast hlenG.symm k)
  simp only [Equiv.trans_apply, finCongr_apply, Equiv.ofBijective_apply]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  simp only [Fin.getElem_fin, Fin.val_cast] at h1 h2
  exact ⟨h2, h1⟩

end Greedy

/-! ### The edges of the observed graph -/

section Edges

variable {d : ℕ}

theorem flip_dir_inj {x : Cube d} {i j : Fin d} (h : flip x i = flip x j) : i = j := by
  by_contra hij
  have := congrFun h i
  rw [flip_apply_self, flip_apply_ne x hij] at this
  cases hx : x i <;> simp [hx] at this

/-- The edge of `Q_d` at `x` in direction `i`, as a pair of names `(u, u')` with `u < u'`. -/
def edgeOf (z : Renaming d) (ix : Fin d × Cube d) : Fin (2 ^ d) × Fin (2 ^ d) :=
  if z.symm ix.2 < z.symm (flip ix.2 ix.1) then (z.symm ix.2, z.symm (flip ix.2 ix.1))
  else (z.symm (flip ix.2 ix.1), z.symm ix.2)

/-- The same edge, as a pair of natural numbers. -/
def edgeNat (z : Renaming d) (ix : Fin d × Cube d) : ℕ × ℕ :=
  ((edgeOf z ix).1, (edgeOf z ix).2)

theorem edgeOf_flip (z : Renaming d) (ix : Fin d × Cube d) :
    z (edgeOf z ix).2 = flip (z (edgeOf z ix).1) ix.1 := by
  unfold edgeOf
  split_ifs <;> simp [flip_flip]

theorem edgeOf_lt (z : Renaming d) (ix : Fin d × Cube d) :
    (edgeOf z ix).1 < (edgeOf z ix).2 := by
  unfold edgeOf
  split_ifs with h
  · exact h
  · have hne : z.symm (flip ix.2 ix.1) ≠ z.symm ix.2 := fun h' ↦
      flip_ne_self ix.2 ix.1 (z.symm.injective h')
    exact lt_of_le_of_ne (not_lt.1 h) hne

theorem edgeOf_lower (z : Renaming d) {ix : Fin d × Cube d} (h : ix.2 ix.1 = false) :
    ix.2 = if z (edgeOf z ix).1 ix.1 = false then z (edgeOf z ix).1 else z (edgeOf z ix).2 := by
  unfold edgeOf
  split_ifs with h1 h2 h2
  · simp
  · simp [h] at h2
  · simp [flip_apply_self, h] at h2
  · simp

open Classical in
/-- The edges of `H`, as pairs `(i, x)` of a direction and the lower endpoint. -/
noncomputable def edgeSet (H : SimpleGraph (Cube d)) : Finset (Fin d × Cube d) :=
  univ.filter fun ix ↦ ix.2 ix.1 = false ∧ H.Adj ix.2 (flip ix.2 ix.1)

theorem mem_edgeSet {H : SimpleGraph (Cube d)} {ix : Fin d × Cube d} :
    ix ∈ edgeSet H ↔ ix.2 ix.1 = false ∧ H.Adj ix.2 (flip ix.2 ix.1) := by
  simp [edgeSet]

/-- The edge list of the observed graph lists the edges of `H`, renamed. -/
theorem mem_edgeList_iff (z : Renaming d) {H : SimpleGraph (Cube d)} (hH : H ≤ cube d)
    (e : ℕ × ℕ) :
    e ∈ Alg.edgeList (2 ^ d) (adjTable (observed H z)) ↔ ∃ ix ∈ edgeSet H, edgeNat z ix = e := by
  obtain ⟨u, v⟩ := e
  have hmem := (Alg.edgeList_adjTable (H.comap z)).2 u v
  rw [show observed H z = ⟨2 ^ d, H.comap z⟩ from rfl, hmem]
  constructor
  · rintro ⟨hu, hv, huv, hadj⟩
    rw [SimpleGraph.comap_adj] at hadj
    obtain ⟨i, hi⟩ := cube_adj_iff.1 (hH hadj)
    have hUV : (⟨u, hu⟩ : Fin (2 ^ d)) < ⟨v, hv⟩ := huv
    cases hb : z ⟨u, hu⟩ i
    · refine ⟨(i, z ⟨u, hu⟩), mem_edgeSet.2 ⟨hb, hi ▸ hadj⟩, ?_⟩
      simp only [edgeNat, edgeOf, Equiv.symm_apply_apply, ← hi, hUV, ite_true]
    · have hflip : flip (z ⟨v, hv⟩) i = z ⟨u, hu⟩ := by rw [hi, flip_flip]
      refine ⟨(i, z ⟨v, hv⟩), mem_edgeSet.2 ⟨?_, ?_⟩, ?_⟩
      · simp only
        rw [hi, flip_apply_self, hb]
        rfl
      · simp only
        rw [hflip]
        exact hadj.symm
      · have hVU : ¬ (⟨v, hv⟩ : Fin (2 ^ d)) < ⟨u, hu⟩ := not_lt.2 hUV.le
        simp only [edgeNat, edgeOf, hflip, Equiv.symm_apply_apply, hVU, ite_false]
  · rintro ⟨ix, hix, he⟩
    simp only [edgeNat, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨_, h2⟩ := mem_edgeSet.1 hix
    refine ⟨(edgeOf z ix).1.isLt, (edgeOf z ix).2.isLt, edgeOf_lt z ix, ?_⟩
    rw [SimpleGraph.comap_adj]
    simp only [Fin.eta]
    unfold edgeOf
    split_ifs
    · simpa using h2
    · simpa using h2.symm

theorem edgeNat_injOn (z : Renaming d) (H : SimpleGraph (Cube d)) :
    Set.InjOn (edgeNat z) (edgeSet H) := by
  intro ix hix jy hjy h
  have h' : edgeOf z ix = edgeOf z jy := by
    simp only [edgeNat, Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  have hi : ix.1 = jy.1 := by
    have h1 := edgeOf_flip z ix
    have h2 := edgeOf_flip z jy
    rw [← h'] at h2
    exact flip_dir_inj (h1.symm.trans h2)
  have hx : ix.2 = jy.2 := by
    rw [edgeOf_lower z (mem_edgeSet.1 (Finset.mem_coe.1 hix)).1,
      edgeOf_lower z (mem_edgeSet.1 (Finset.mem_coe.1 hjy)).1, h', hi]
  exact Prod.ext hi hx

theorem card_edgeSet (H : SimpleGraph (Cube d)) : #(edgeSet H) = ∑ i, dirCount H i := by
  classical
  simp only [edgeSet, dirCount, card_filter]
  rw [Fintype.sum_prod_type]

theorem card_edgeSet_dir (H : SimpleGraph (Cube d)) (i : Fin d) :
    #((edgeSet H).filter fun ix ↦ ix.1 = i) = dirCount H i := by
  classical
  rw [edgeSet, filter_filter, card_filter, Fintype.sum_prod_type, dirCount, card_filter,
    Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

end Edges

/-! ### Sign vectors of edges and their errors -/

section Errors

variable {d : ℕ}

/-- The coordinate cut `χ̂ᵢ` as a bit list: bit `v` is `z v i`. -/
def cutL (z : Renaming d) (i : Fin d) : List Bool := List.ofFn fun v : Fin (2 ^ d) ↦ z v i

theorem length_cutL (z : Renaming d) (i : Fin d) : (cutL z i).length = 2 ^ d := by
  simp [cutL]

theorem length_edgeVec (n : ℕ) (Mt : List (List ℚ)) (e : ℕ × ℕ) :
    (Round.edgeVec n Mt e).length = n := by
  simp [Round.edgeVec]

theorem bitF_edgeVec (n : ℕ) (Mt : List (List ℚ)) (e : ℕ × ℕ) (v : Fin n) :
    bitF n (Round.edgeVec n Mt e) v = decide (Round.entry Mt e.1 v < Round.entry Mt e.2 v) := by
  simp [bitF, Round.edgeVec, List.getD_eq_getElem?_getD]

/-- Two different coordinate cuts differ in exactly half of the positions. -/
theorem two_mul_hammPM_cutL (z : Renaming d) {i j : Fin d} (hij : i ≠ j) :
    2 * Round.hammPM (2 ^ d) (cutL z i) (cutL z j) = 2 ^ d := by
  have hf : 2 * fdist (fun v : Fin (2 ^ d) ↦ z v i) (fun v ↦ z v j) = 2 ^ d := by
    have h1 : ∑ v : Fin (2 ^ d), sgn (z v i) * sgn (z v j) = 0 := by
      rw [Equiv.sum_comp z (fun x ↦ sgn (x i) * sgn (x j))]
      have := sum_chi_mul_chi (m := d) {i} {j}
      simp only [chi_singleton, Finset.singleton_inj, ite_eq_right hij] at this
      exact this
    have h2 : ∀ v : Fin (2 ^ d), sgn (z v i) * sgn (z v j) =
        1 - 2 * (if z v i ≠ z v j then 1 else 0 : ℝ) := by
      intro v
      cases z v i <;> cases z v j <;> norm_num [sgn]
    have h3 : ((2 * fdist (fun v : Fin (2 ^ d) ↦ z v i) (fun v ↦ z v j) : ℕ) : ℝ) = 2 ^ d := by
      rw [fdist, card_filter]
      push_cast
      simp_rw [h2] at h1
      rw [sum_sub_distrib, ← mul_sum] at h1
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1
      push_cast at h1
      linarith
    exact_mod_cast h3
  have hf' := fdist_le (fun v : Fin (2 ^ d) ↦ z v i) (fun v ↦ z v j)
  rw [hammPM_eq (length_cutL z i) (length_cutL z j), cutL, cutL, bitF_ofFn, bitF_ofFn]
  omega

/-- The squared error of the row `u` of the moment table. -/
noncomputable def rowErr (z : Renaming d) (Mt : List (List ℚ)) (u : Fin (2 ^ d)) : ℝ :=
  ∑ v : Fin (2 ^ d), ((Round.entry Mt u v : ℝ) - targetM z u v) ^ 2

theorem rowErr_nonneg (z : Renaming d) (Mt : List (List ℚ)) (u : Fin (2 ^ d)) :
    0 ≤ rowErr z Mt u :=
  sum_nonneg fun _ _ ↦ sq_nonneg _

theorem rowErr_edgeOf (z : Renaming d) (Mt : List (List ℚ)) (ix : Fin d × Cube d) :
    rowErr z Mt (edgeOf z ix).1 + rowErr z Mt (edgeOf z ix).2 =
      rowErr z Mt (z.symm ix.2) + rowErr z Mt (z.symm (flip ix.2 ix.1)) := by
  unfold edgeOf
  split_ifs
  · rfl
  · exact add_comm _ _

theorem sum_rowErr_edgeSet (z : Renaming d) (Mt : List (List ℚ)) (H : SimpleGraph (Cube d)) :
    ∑ ix ∈ edgeSet H, (rowErr z Mt (z.symm ix.2) + rowErr z Mt (z.symm (flip ix.2 ix.1))) ≤
      2 * d * ∑ u, rowErr z Mt u := by
  calc _ ≤ ∑ ix : Fin d × Cube d,
        (rowErr z Mt (z.symm ix.2) + rowErr z Mt (z.symm (flip ix.2 ix.1))) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun ix _ _ ↦
          add_nonneg (rowErr_nonneg _ _ _) (rowErr_nonneg _ _ _)
    _ = ∑ i : Fin d, (∑ x, rowErr z Mt (z.symm x) + ∑ x, rowErr z Mt (z.symm (flip x i))) := by
        rw [Fintype.sum_prod_type]
        simp only [sum_add_distrib]
    _ = ∑ _i : Fin d, 2 * ∑ u, rowErr z Mt u := by
        refine sum_congr rfl fun i _ ↦ ?_
        have h1 : ∑ x, rowErr z Mt (z.symm x) = ∑ u, rowErr z Mt u :=
          Equiv.sum_comp z.symm _
        have h2 : ∑ x, rowErr z Mt (z.symm (flip x i)) = ∑ x, rowErr z Mt (z.symm x) :=
          Equiv.sum_comp (Function.Involutive.toPerm (fun x ↦ flip x i) (fun x ↦ flip_flip x i))
            (fun x ↦ rowErr z Mt (z.symm x))
        rw [h2, h1]
        ring
    _ = 2 * d * ∑ u, rowErr z Mt u := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The number of wrong bits of the sign vector of the oriented edge `(u, u')` in direction
`i`, compared with the cut `χ̂ᵢ(u) χ̂ᵢ`. -/
def errE (z : Renaming d) (Mt : List (List ℚ)) (u u' : Fin (2 ^ d)) (i : Fin d) : ℕ :=
  #{v : Fin (2 ^ d) | decide (Round.entry Mt u v < Round.entry Mt u' v) ≠ xor (z u i) (z v i)}

theorem targetM_sub (z : Renaming d) {u u' : Fin (2 ^ d)} {i : Fin d}
    (h : z u' = flip (z u) i) (v : Fin (2 ^ d)) :
    targetM z u' v - targetM z u v = -(2 / d) * (sgn (z u i) * sgn (z v i)) := by
  rw [targetM, targetM, ← sub_div, ← sum_sub_distrib, Finset.sum_eq_single i]
  · rw [h, flip_apply_self, sgn_not]
    ring
  · intro j _ hj
    rw [h, flip_apply_ne _ hj]
    ring
  · simp

/-- **The error of an edge**: a wrong bit at `v` costs at least `4/d²` in the squared errors of
the rows `u` and `u'` at `v`. -/
theorem errE_le (z : Renaming d) (Mt : List (List ℚ)) {u u' : Fin (2 ^ d)} {i : Fin d}
    (hd : 0 < d) (h : z u' = flip (z u) i) :
    (errE z Mt u u' i : ℝ) ≤ (d : ℝ) ^ 2 / 2 * (rowErr z Mt u + rowErr z Mt u') := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [errE, card_filter]
  push_cast
  rw [rowErr, rowErr, ← sum_add_distrib, mul_sum]
  refine sum_le_sum fun v _ ↦ ?_
  split_ifs with hv
  · have hD := targetM_sub z h v
    have hcases : ((Round.entry Mt u v : ℝ) < Round.entry Mt u' v ∧
          sgn (z u i) * sgn (z v i) = 1) ∨
        ((Round.entry Mt u' v : ℝ) ≤ Round.entry Mt u v ∧ sgn (z u i) * sgn (z v i) = -1) := by
      cases hu : z u i <;> cases hv' : z v i <;>
        simp only [hu, hv', sgn, bne_self_eq_false, Bool.bne_true, Bool.bne_false, Bool.not_false,
          ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, not_lt, not_le, Rat.cast_lt,
          Rat.cast_le, Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one, neg_neg, and_true]
          at hv ⊢ <;>
        first
        | exact Or.inl (by exact_mod_cast hv)
        | exact Or.inr (by exact_mod_cast hv)
    have ht : (((Round.entry Mt u' v : ℝ) - targetM z u' v) -
        ((Round.entry Mt u v : ℝ) - targetM z u v)) * d =
        ((Round.entry Mt u' v : ℝ) - Round.entry Mt u v) * d +
          2 * (sgn (z u i) * sgn (z v i)) := by
      rw [show ((Round.entry Mt u' v : ℝ) - targetM z u' v) -
          ((Round.entry Mt u v : ℝ) - targetM z u v) =
          ((Round.entry Mt u' v : ℝ) - Round.entry Mt u v) -
            (targetM z u' v - targetM z u v) by ring, hD]
      field_simp
      ring
    have hsq : 4 ≤ ((((Round.entry Mt u' v : ℝ) - targetM z u' v) -
        ((Round.entry Mt u v : ℝ) - targetM z u v)) * d) ^ 2 := by
      rw [ht]
      rcases hcases with ⟨hlt, hs⟩ | ⟨hlt, hs⟩
      · rw [hs]
        have : 0 < ((Round.entry Mt u' v : ℝ) - Round.entry Mt u v) * d :=
          mul_pos (by linarith) hd'
        nlinarith
      · rw [hs]
        have : ((Round.entry Mt u' v : ℝ) - Round.entry Mt u v) * d ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hd'.le
        nlinarith
    nlinarith [sq_nonneg ((((Round.entry Mt u v : ℝ) - targetM z u v) +
      ((Round.entry Mt u' v : ℝ) - targetM z u' v)) * d)]
  · positivity

/-- The sign vector of an edge is within its error of the cut, up to sign. -/
theorem hammPM_edgeVec_le (z : Renaming d) (Mt : List (List ℚ)) (u u' : Fin (2 ^ d))
    (i : Fin d) :
    Round.hammPM (2 ^ d) (Round.edgeVec (2 ^ d) Mt (u, u')) (cutL z i) ≤ errE z Mt u u' i := by
  have := hammPM_ofFn_le (length_edgeVec (2 ^ d) Mt (u, u')) (fun v ↦ z v i) (z u i)
  rw [cutL]
  refine this.trans_eq ?_
  simp only [errE, fdist, bitF_edgeVec]

end Errors

/-! ### Counting sign vectors of edges, and the output -/

section Bridge

variable {d : ℕ}

/-- Counting the sign vectors of the observed edges is counting the edges of `H`. -/
theorem countP_edgeVec (z : Renaming d) {H : SimpleGraph (Cube d)} (hH : H ≤ cube d)
    (Mt : List (List ℚ)) (q : List Bool → Bool) :
    ((Alg.edgeList (2 ^ d) (adjTable (observed H z))).map (Round.edgeVec (2 ^ d) Mt)).countP q =
      #((edgeSet H).filter fun ix ↦ q (Round.edgeVec (2 ^ d) Mt (edgeNat z ix)) = true) := by
  classical
  have hnd : (Alg.edgeList (2 ^ d) (adjTable (observed H z))).Nodup :=
    (Alg.edgeList_adjTable (H.comap z)).1
  have hfin : (Alg.edgeList (2 ^ d) (adjTable (observed H z))).toFinset =
      (edgeSet H).image (edgeNat z) := by
    ext e
    rw [List.mem_toFinset, mem_image, mem_edgeList_iff z hH]
  rw [List.countP_map, List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _),
    List.toFinset_filter, hfin, filter_image, card_image_of_injOn]
  · rfl
  · exact (edgeNat_injOn z H).mono fun x hx ↦ (mem_filter.1 (Finset.mem_coe.1 hx)).1

/-- The number of observed edges. -/
theorem length_edgeList (z : Renaming d) {H : SimpleGraph (Cube d)} (hH : H ≤ cube d) :
    (Alg.edgeList (2 ^ d) (adjTable (observed H z))).length = ∑ i, dirCount H i := by
  have := countP_edgeVec z hH [] (fun _ ↦ true)
  simp only [List.countP_true, List.length_map] at this
  rw [this, Finset.filter_true, card_edgeSet]

/-- The output vectors are read off the kept vectors. -/
theorem outVec_roundOut (n d c : ℕ) (Mt : List (List ℚ)) (edges : List (ℕ × ℕ)) {v : ℕ}
    (hv : v < n) (i : Fin d) :
    outVec d (Round.roundOut n d c Mt edges) v i =
      ((Round.greedy n (n / d ^ (c + 2)) (edges.length / (4 * d))
        (edges.map (Round.edgeVec n Mt))).getD i []).getD v false := by
  simp only [outVec, Round.roundOut, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hv, Option.map_some, Option.getD_some, List.getElem?_take, i.2, ite_true]
  generalize (Round.greedy n (n / d ^ (c + 2)) (edges.length / (4 * d))
    (edges.map (Round.edgeVec n Mt)))[(i : ℕ)]? = o
  cases o <;> rfl

end Bridge

end Rnd

open Rnd in
/-- **The rounding recovers the hidden vectors.** -/
theorem roundOut_recovers (c : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (z : Renaming d) (H : SimpleGraph (Cube d)), H ≤ cube d →
      ∀ p τ₀ : ℝ, 1 / (d : ℝ) ≤ p → p ≤ 1 → 0 ≤ τ₀ → τ₀ ≤ 1 / 4 →
      (∀ i, |(dirCount H i : ℝ) - p * 2 ^ d / 2| ≤ τ₀ * (p * 2 ^ d / 2)) →
      ∀ Mt : List (List ℚ),
        ∑ u : Fin (2 ^ d), ∑ v : Fin (2 ^ d), ((Round.entry Mt u v : ℝ) - targetM z u v) ^ 2 ≤
          p * 4 ^ d / (64 * (d : ℝ) ^ (c + 5)) →
        Recovers z (2 ^ d / (d : ℝ) ^ c)
          (Round.roundOut (2 ^ d) d c Mt (Alg.edgeList (2 ^ d) (adjTable (observed H z)))) := by
  refine ⟨32, fun d hd z H hH p τ₀ hp1 _ _ hτ1 hcount Mt hF ↦ ?_⟩
  classical
  have hd0 : 0 < d := by omega
  have hdR : (32 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp1
  set E := Alg.edgeList (2 ^ d) (adjTable (observed H z)) with hE
  set vs := E.map (Round.edgeVec (2 ^ d) Mt) with hvs
  set T := 2 ^ d / d ^ (c + 2) with hT
  set mth := E.length / (4 * d) with hmth
  set er : Fin d × Cube d → ℕ := fun ix ↦ errE z Mt (edgeOf z ix).1 (edgeOf z ix).2 ix.1
    with her
  set B := #((edgeSet H).filter fun ix ↦ T < er ix) with hB
  /- Sizes. -/
  have hNR : (0 : ℝ) < 2 ^ d := by positivity
  have hdc : (0 : ℝ) < (d : ℝ) ^ (c + 2) := by positivity
  have hTle : (T : ℝ) ≤ 2 ^ d / (d : ℝ) ^ (c + 2) := by
    have := Nat.cast_div_le (α := ℝ) (m := 2 ^ d) (n := d ^ (c + 2))
    simpa using this
  have hTgt : 2 ^ d / (d : ℝ) ^ (c + 2) < T + 1 := by
    have h := Nat.lt_div_mul_add (a := 2 ^ d) (b := d ^ (c + 2)) (by positivity)
    have h' : ((2 ^ d : ℕ) : ℝ) < ((T * d ^ (c + 2) + d ^ (c + 2) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    rw [div_lt_iff₀ hdc]
    linarith
  have h2d : (16 : ℝ) * d ≤ 2 ^ d := by
    have h1 := Nat.lt_two_pow_self (n := d - 5)
    have h2 : 2 ^ d = 2 ^ (d - 5) * 32 := by
      rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_add]
      congr 1
      omega
    have h3 : 16 * d ≤ 2 ^ d := by
      rw [h2]
      generalize 2 ^ (d - 5) = M at h1
      omega
    exact_mod_cast h3
  have hpN : 16 ≤ p * 2 ^ d := by
    have h1 : 1 / (d : ℝ) * 2 ^ d ≤ p * 2 ^ d := mul_le_mul_of_nonneg_right hp1 hNR.le
    have h2 : 16 ≤ 1 / (d : ℝ) * 2 ^ d := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hdpos]
      linarith
    linarith
  have hdir : ∀ i, 3 * p * 2 ^ d / 8 ≤ (dirCount H i : ℝ) ∧
      (dirCount H i : ℝ) ≤ 5 * p * 2 ^ d / 8 := by
    intro i
    have h := abs_le.1 (hcount i)
    have h0 : 0 ≤ (1 / 4 - τ₀) * (p * 2 ^ d / 2) :=
      mul_nonneg (by linarith) (by positivity)
    constructor <;> nlinarith [h.1, h.2]
  have hElen : (E.length : ℝ) = ∑ i, (dirCount H i : ℝ) := by
    rw [hE, length_edgeList z hH]
    push_cast
    rfl
  have hElo : 3 * d * p * 2 ^ d / 8 ≤ (E.length : ℝ) := by
    rw [hElen]
    calc 3 * d * p * 2 ^ d / 8 = ∑ _i : Fin d, 3 * p * 2 ^ d / 8 := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ _ := sum_le_sum fun i _ ↦ (hdir i).1
  have hEhi : (E.length : ℝ) ≤ 5 * d * p * 2 ^ d / 8 := by
    rw [hElen]
    calc _ ≤ ∑ _i : Fin d, 5 * p * 2 ^ d / 8 := sum_le_sum fun i _ ↦ (hdir i).2
      _ = 5 * d * p * 2 ^ d / 8 := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hmth_le : (mth : ℝ) ≤ 5 * p * 2 ^ d / 32 := by
    have h := Nat.cast_div_le (α := ℝ) (m := E.length) (n := 4 * d)
    refine h.trans ?_
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hmth_gt : 3 * p * 2 ^ d / 32 - 1 < mth := by
    have h := Nat.lt_div_mul_add (a := E.length) (b := 4 * d) (by omega)
    have h' : (E.length : ℝ) < (mth : ℝ) * (4 * d) + 4 * d := by exact_mod_cast h
    by_contra hcon
    push Not at hcon
    have h3 := mul_le_mul_of_nonneg_right hcon (by positivity : (0 : ℝ) ≤ 4 * d)
    nlinarith
  /- The total error of the edges, and the bad edges. -/
  have hFR : ∑ u, rowErr z Mt u ≤ p * 4 ^ d / (64 * (d : ℝ) ^ (c + 5)) := hF
  have hsumerr : ∑ ix ∈ edgeSet H, (er ix : ℝ) ≤ (d : ℝ) ^ 3 * ∑ u, rowErr z Mt u := by
    calc ∑ ix ∈ edgeSet H, (er ix : ℝ)
        ≤ ∑ ix ∈ edgeSet H, (d : ℝ) ^ 2 / 2 *
            (rowErr z Mt (z.symm ix.2) + rowErr z Mt (z.symm (flip ix.2 ix.1))) :=
          sum_le_sum fun ix _ ↦
            (errE_le z Mt hd0 (edgeOf_flip z ix)).trans_eq (by rw [rowErr_edgeOf])
      _ = (d : ℝ) ^ 2 / 2 * ∑ ix ∈ edgeSet H,
            (rowErr z Mt (z.symm ix.2) + rowErr z Mt (z.symm (flip ix.2 ix.1))) :=
          (mul_sum _ _ _).symm
      _ ≤ (d : ℝ) ^ 2 / 2 * (2 * d * ∑ u, rowErr z Mt u) :=
          mul_le_mul_of_nonneg_left (sum_rowErr_edgeSet z Mt H) (by positivity)
      _ = _ := by ring
  have hBb : (B : ℝ) ≤ p * 2 ^ d / 64 := by
    have h1 : (B : ℝ) * (T + 1) ≤ ∑ ix ∈ edgeSet H, (er ix : ℝ) := by
      calc (B : ℝ) * (T + 1) = ∑ ix ∈ (edgeSet H).filter (fun ix ↦ T < er ix), ((T : ℝ) + 1) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ ix ∈ (edgeSet H).filter (fun ix ↦ T < er ix), (er ix : ℝ) :=
            sum_le_sum fun ix hix ↦ by
              have := (mem_filter.1 hix).2
              exact_mod_cast Nat.succ_le_of_lt this
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ Nat.cast_nonneg _
    have h4 : (4 : ℝ) ^ d = 2 ^ d * 2 ^ d := by
      rw [← mul_pow]
      norm_num
    have h2 : (d : ℝ) ^ 3 * (p * 4 ^ d / (64 * (d : ℝ) ^ (c + 5))) =
        p * 2 ^ d / 64 * (2 ^ d / (d : ℝ) ^ (c + 2)) := by
      rw [h4]
      field_simp
      ring
    have h3 : (B : ℝ) * (2 ^ d / (d : ℝ) ^ (c + 2)) ≤
        p * 2 ^ d / 64 * (2 ^ d / (d : ℝ) ^ (c + 2)) := by
      calc _ ≤ (B : ℝ) * (T + 1) := mul_le_mul_of_nonneg_left hTgt.le (Nat.cast_nonneg _)
        _ ≤ _ := h1
        _ ≤ _ := hsumerr
        _ ≤ (d : ℝ) ^ 3 * (p * 4 ^ d / (64 * (d : ℝ) ^ (c + 5))) :=
            mul_le_mul_of_nonneg_left hFR (by positivity)
        _ = _ := h2
    exact le_of_mul_le_mul_right h3 (by positivity)
  /- The hypotheses of the clustering lemma. -/
  have hlen : ∀ a ∈ vs, a.length = 2 ^ d := by
    intro a ha
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
    exact length_edgeVec _ _ _
  have hN4 : 2 ^ d = 4 * 2 ^ (d - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hT24 : 24 * T < 2 ^ d := by
    have h1 : T * d ^ (c + 2) ≤ 2 ^ d := Nat.div_mul_le_self _ _
    have h2 : 25 ≤ d ^ (c + 2) := by
      calc 25 ≤ d ^ 2 := by nlinarith
        _ ≤ d ^ (c + 2) := Nat.pow_le_pow_right hd0 (by omega)
    have h3 : 25 * T ≤ T * d ^ (c + 2) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left T h2
    have h4 : 0 < 2 ^ d := by positivity
    omega
  have hsep : ∀ i j, i ≠ j → 2 ^ d / 4 + 6 * T < Round.hammPM (2 ^ d) (cutL z i) (cutL z j) := by
    intro i j hij
    have := two_mul_hammPM_cutL z hij
    omega
  have hT6 : 6 * T ≤ 2 ^ d / 4 := by omega
  have hbad : vs.countP (fun a ↦ decide (∀ i, T < Round.hammPM (2 ^ d) a (cutL z i))) < mth := by
    rw [hvs, hE, countP_edgeVec z hH Mt]
    have h1 : #((edgeSet H).filter fun ix ↦ decide (∀ i, T < Round.hammPM (2 ^ d)
        (Round.edgeVec (2 ^ d) Mt (edgeNat z ix)) (cutL z i)) = true) ≤ B := by
      refine card_le_card fun ix hix ↦ ?_
      simp only [mem_filter, decide_eq_true_eq] at hix ⊢
      exact ⟨hix.1, lt_of_lt_of_le (hix.2 ix.1) (hammPM_edgeVec_le z Mt _ _ ix.1)⟩
    have h2 : (B : ℝ) < mth := by linarith
    have h3 : B < mth := by exact_mod_cast h2
    omega
  have hgood : ∀ i, mth ≤ vs.countP (fun a ↦ decide (Round.hammPM (2 ^ d) a (cutL z i) ≤ T)) := by
    intro i
    rw [hvs, hE, countP_edgeVec z hH Mt]
    have h1 : (edgeSet H).filter (fun ix ↦ ix.1 = i) ⊆
        (edgeSet H).filter (fun ix ↦ decide (Round.hammPM (2 ^ d)
          (Round.edgeVec (2 ^ d) Mt (edgeNat z ix)) (cutL z i) ≤ T) = true) ∪
        (edgeSet H).filter (fun ix ↦ T < er ix) := by
      intro ix hix
      simp only [mem_filter, mem_union, decide_eq_true_eq] at hix ⊢
      by_cases he : T < er ix
      · exact Or.inr ⟨hix.1, he⟩
      · refine Or.inl ⟨hix.1, ?_⟩
        rw [← hix.2]
        exact (hammPM_edgeVec_le z Mt _ _ ix.1).trans (not_lt.1 he)
    have h2 := (card_le_card h1).trans (card_union_le _ _)
    rw [card_edgeSet_dir, ← hB] at h2
    have h3 : (mth : ℝ) + B ≤ dirCount H i := by linarith [(hdir i).1]
    have h4 : mth + B ≤ dirCount H i := by exact_mod_cast h3
    omega
  /- The clustering, and the signs of the kept vectors. -/
  obtain ⟨-, σ, hσ⟩ := greedy_spec (cutL z) hlen (length_cutL z) hsep hT6 hbad hgood
  have ht : ∀ k : Fin d, ∃ t : Bool,
      fdist (bitF (2 ^ d) ((Round.greedy (2 ^ d) T mth vs).getD k []))
        (fun v ↦ xor t (z v (σ k))) ≤ 3 * T := fun k ↦
    exists_of_hammPM_ofFn_le (hσ k).1 (fun v ↦ z v (σ k)) (hσ k).2
  choose t ht using ht
  refine ⟨σ.symm, fun i ↦ t (σ.symm i), ?_⟩
  have hsub : (univ.filter fun v : Fin (2 ^ d) ↦ cubeAut σ.symm (fun i ↦ t (σ.symm i))
      (outVec d (Round.roundOut (2 ^ d) d c Mt E) v) ≠ z v) ⊆
      univ.biUnion fun k : Fin d ↦ univ.filter fun v : Fin (2 ^ d) ↦
        bitF (2 ^ d) ((Round.greedy (2 ^ d) T mth vs).getD k []) v ≠ xor (t k) (z v (σ k)) := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and, mem_biUnion] at hv ⊢
    by_contra hcon
    push Not at hcon
    apply hv
    funext i
    simp only [cubeAut]
    rw [outVec_roundOut (2 ^ d) d c Mt E v.2 (σ.symm i)]
    have h1 := hcon (σ.symm i)
    rw [Equiv.apply_symm_apply] at h1
    change xor _ (bitF (2 ^ d) ((Round.greedy (2 ^ d) T mth vs).getD (σ.symm i) []) v) = _
    rw [h1]
    cases t (σ.symm i) <;> simp
  refine le_trans (Nat.cast_le.2 ((card_le_card hsub).trans card_biUnion_le)) ?_
  push_cast
  calc _ ≤ ∑ _k : Fin d, (3 * T : ℝ) := sum_le_sum fun k _ ↦ by exact_mod_cast ht k
    _ = 3 * d * T := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ 3 * d * (2 ^ d / (d : ℝ) ^ (c + 2)) := by gcongr
    _ = 3 / d * (2 ^ d / (d : ℝ) ^ c) := by
        field_simp
        ring
    _ ≤ 1 * (2 ^ d / (d : ℝ) ^ c) := by
        gcongr
        rw [div_le_one hdpos]
        linarith
    _ = _ := one_mul _

end BMW26
