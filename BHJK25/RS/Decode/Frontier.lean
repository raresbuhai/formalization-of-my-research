module

public import BHJK25.RS.Decode.RRLists
public import BHJK25.RS.Decode.RothRuckenstein
public import Mathlib.Data.List.GetD

/-!
# The per-guess decoder: the levels of Roth–Ruckenstein

The nodes of `BHJK25.RS.DecodeAux.rrRoots` are read in the field, in the window `j < W + 1`,
`i < L = (m + 1)(W + 1)`. Suppose that `elts` lists every field element exactly once.

* **Validity.** A node of level `ℓ` is *valid* when its polynomial `Q` has `Q(0, Y) ≠ 0` and
  `X`-degrees at most `W + ℓ W`. The children of a valid node of level `ℓ < m` are the children of
  `BHJK25.RS.RR`, divided by powers of `X`: the window is large enough
  (`BHJK25.RS.DecodeAux.Sem.toBP_child`), and they are valid nodes of level `ℓ + 1`.
* **Counting.** By the multiplicity bound, a valid node `Q` has at most `deg Q(0, Y)` children,
  whose degrees `deg Q'(0, Y)` sum to at most `deg Q(0, Y)`
  (`BHJK25.RS.DecodeAux.Sem.children_spec`). Hence the degrees of the nodes of a level sum to at
  most `W`, and each level has at most `W` nodes before the truncation to `W + 1` nodes, which
  never drops a node (`BHJK25.RS.DecodeAux.Sem.level_spec`).
* **Completeness** (`BHJK25.RS.DecodeAux.Sem.rrRoots_complete`): if the initial polynomial is
  nonzero, has `X`-degrees at most `W`, and vanishes at `Y = p(X)`, then some candidate starts with
  the first `m` coefficients of `p`: at level `ℓ`, the node with the first `ℓ` coefficients of `p`
  vanishes at `Y = (p - (p mod X^ℓ)) / X^ℓ`.
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux

/-- The type of nodes: a bivariate polynomial and the coefficients found so far. -/
abbrev Node : Type := List (List (List ℕ)) × List (List ℕ)

namespace Sem

open Polynomial

variable {fl : List ℕ} {F : Type*} [Field F] (S : Sem fl F)

/-! ### List helpers -/

private theorem length_eq_sum_map_one {α : Type*} (l : List α) :
    l.length = (l.map fun _ ↦ 1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.length_cons, List.map_cons, List.sum_cons, ih, add_comm]

private theorem sum_map_flatMap {α β : Type*} (l : List α) (g : α → List β) (f : β → ℕ) :
    ((l.flatMap g).map f).sum = (l.map fun a ↦ ((g a).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]

private theorem foldl_range_eq_iterate {α : Type*} (f : α → α) (x : α) (ℓ : ℕ) :
    (List.range ℓ).foldl (fun y _ ↦ f y) x = f^[ℓ] x := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ_apply']; rfl

/-! ### Nodes -/

/-- The polynomial of a node. -/
noncomputable def nodeP (m W : ℕ) (nd : Node) : F[X][X] :=
  S.toBP (W + 1) ((m + 1) * (W + 1)) nd.1

/-- The degree of `Q(0, Y)` for the polynomial `Q` of a node. -/
noncomputable def nodeD (m W : ℕ) (nd : Node) : ℕ :=
  ((S.nodeP m W nd).map constantCoeff).natDegree

/-- A node of level `ℓ` is valid when its polynomial `Q` has `Q(0, Y) ≠ 0` and `X`-degrees at
most `W + ℓ W`. -/
def Valid (m W ℓ : ℕ) (nd : Node) : Prop :=
  (S.nodeP m W nd).map constantCoeff ≠ 0 ∧ ∀ j, ((S.nodeP m W nd).coeff j).natDegree ≤ W + ℓ * W

theorem nodeD_le (m W : ℕ) (nd : Node) : S.nodeD m W nd ≤ W := by
  have h := S.natDegree_toBP_lt (L := (m + 1) * (W + 1)) (Nat.succ_pos W) nd.1
  exact Nat.lt_succ_iff.mp (natDegree_map_le.trans_lt h)

/-- The window is large enough: the child of a valid node of level `ℓ < m` is computed
exactly. -/
theorem toBP_child {m W ℓ : ℕ} {nd : Node} (hv : S.Valid m W ℓ nd) (hℓ : ℓ < m)
    (c : List ℕ) :
    S.toBP (W + 1) ((m + 1) * (W + 1))
        (shiftL fl (W + 1) ((m + 1) * (W + 1)) (taylorL fl (W + 1) ((m + 1) * (W + 1)) nd.1 c)) =
      RR.child (S.nodeP m W nd) (S.ev c) := by
  rw [S.toBP_shiftL, S.toBP_taylorL (Nat.succ_pos W)]
  · rfl
  intro j i hji
  have hw := S.lt_of_coeff_coeff_toBP_ne_zero hji
  rw [S.toBP_taylorL (Nat.succ_pos W)] at hji
  have hi : i ≤ W + ℓ * W :=
    (le_natDegree_of_ne_zero hji).trans (RR.natDegree_taylor_coeff_le hv.2 _ _)
  have hj : j ≤ W := Nat.lt_succ_iff.mp hw.1
  have h1 : (ℓ + 2) * W ≤ (m + 1) * W := Nat.mul_le_mul_right _ (by omega)
  have h2 : (m + 1) * (W + 1) = (m + 1) * W + (m + 1) := by ring
  have h3 : (ℓ + 2) * W = W + ℓ * W + W := by ring
  omega

/-- The child node at `c`. -/
def childNode (m W : ℕ) (nd : Node) (c : List ℕ) : Node :=
  (stripL fl (W + 1) ((m + 1) * (W + 1))
    (shiftL fl (W + 1) ((m + 1) * (W + 1)) (taylorL fl (W + 1) ((m + 1) * (W + 1)) nd.1 c)),
    ((nd.2 ++ [c]).map fun e ↦ fadd fl e (fzero fl)).take m)

omit [Field F] in
theorem children_eq (elts : List (List ℕ)) (m W : ℕ) (nd : Node) :
    children fl elts m (W + 1) ((m + 1) * (W + 1)) nd =
      (elts.filter fun c ↦ isZ fl (eval0 fl (W + 1) nd.1 c)).map (childNode (fl := fl) m W nd) :=
  rfl

/-- The child of a valid node is the child of `BHJK25.RS.RR`, divided by a power of `X`. -/
theorem childNode_spec {m W ℓ : ℕ} {nd : Node} (hv : S.Valid m W ℓ nd) (hℓ : ℓ < m)
    (c : List ℕ) : ∃ v, RR.child (S.nodeP m W nd) (S.ev c) =
      C (X ^ v) * S.nodeP m W (childNode (fl := fl) m W nd c) ∧
      (S.nodeP m W (childNode (fl := fl) m W nd c)).map constantCoeff ≠ 0 := by
  have hne : RR.child (S.nodeP m W nd) (S.ev c) ≠ 0 := by
    refine RR.child_ne_zero (fun h ↦ hv.1 ?_) _
    rw [h, Polynomial.map_zero]
  rw [← S.toBP_child hv hℓ c] at hne ⊢
  exact S.toBP_stripL _ hne

/-- A child of a valid node of level `ℓ < m` is valid at level `ℓ + 1`, and its degree at
`X = 0` is at most the multiplicity of `c`. -/
theorem childNode_valid {m W ℓ : ℕ} {nd : Node} (hv : S.Valid m W ℓ nd) (hℓ : ℓ < m)
    (c : List ℕ) : S.Valid m W (ℓ + 1) (childNode (fl := fl) m W nd c) ∧
      S.nodeD m W (childNode (fl := fl) m W nd c) ≤
        rootMultiplicity (S.ev c) ((S.nodeP m W nd).map constantCoeff) := by
  obtain ⟨v, hv', hne⟩ := S.childNode_spec hv hℓ c
  refine ⟨⟨hne, fun j ↦ ?_⟩, RR.natDegree_map_le_rootMultiplicity hv.1 hv'⟩
  set Q₁ := S.nodeP m W (childNode (fl := fl) m W nd c)
  rcases eq_or_ne (Q₁.coeff j) 0 with h0 | h0
  · rw [h0, natDegree_zero]
    exact Nat.zero_le _
  have hj : j ≤ W := by
    obtain ⟨i, hi⟩ : ∃ i, (Q₁.coeff j).coeff i ≠ 0 := by
      by_contra h
      exact h0 (Polynomial.ext fun i ↦ by by_contra hi; exact h ⟨i, hi⟩)
    exact Nat.lt_succ_iff.mp (S.lt_of_coeff_coeff_toBP_ne_zero hi).1
  have hc := congrArg (fun P ↦ P.coeff j) hv'
  simp only [coeff_C_mul, RR.child_coeff] at hc
  have h1 : (Q₁.coeff j).natDegree ≤ (X ^ v * Q₁.coeff j).natDegree := by
    rw [natDegree_X_pow_mul _ h0]
    exact Nat.le_add_right _ _
  have h2 := natDegree_mul_le (p := (taylor (C (S.ev c)) (S.nodeP m W nd)).coeff j)
    (q := (X ^ j : F[X]))
  have h3 := RR.natDegree_taylor_coeff_le hv.2 (S.ev c) j
  rw [natDegree_X_pow] at h2
  rw [← hc] at h1
  have h4 : (ℓ + 1) * W = ℓ * W + W := by ring
  omega

omit [Field F] in
theorem childNode_length {m : ℕ} (W : ℕ) {nd : Node} (h : nd.2.length < m) (c : List ℕ) :
    (childNode (fl := fl) m W nd c).2.length = nd.2.length + 1 := by
  simp only [childNode, List.length_take, List.length_map, List.length_append,
    List.length_singleton]
  omega

/-- The coefficients of a child, read in the field. -/
theorem ev_getD_childNode (m W : ℕ) (nd : Node) (c : List ℕ) {i : ℕ} (hi : i < m)
    (hl : i < nd.2.length + 1) :
    S.ev ((childNode (fl := fl) m W nd c).2.getD i []) = S.ev ((nd.2 ++ [c]).getD i []) := by
  simp only [childNode]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, List.getElem_map,
    List.getD_eq_getElem _ _ (by simpa using hl), S.ev_add, S.ev_zero, add_zero]

/-! ### Counting -/

/-- **The children of a valid node.** They are valid at the next level; there are at most
`deg Q(0, Y)` of them, and their degrees at `X = 0` sum to at most `deg Q(0, Y)`. -/
theorem children_spec {elts : List (List ℕ)} (hnd : (elts.map S.ev).Nodup) {m W ℓ : ℕ}
    {nd : Node} (hv : S.Valid m W ℓ nd) (hℓ : ℓ < m) :
    (∀ ch ∈ children fl elts m (W + 1) ((m + 1) * (W + 1)) nd, S.Valid m W (ℓ + 1) ch) ∧
      (children fl elts m (W + 1) ((m + 1) * (W + 1)) nd).length ≤ S.nodeD m W nd ∧
      ((children fl elts m (W + 1) ((m + 1) * (W + 1)) nd).map (S.nodeD m W)).sum ≤
        S.nodeD m W nd := by
  rw [children_eq]
  set q := (S.nodeP m W nd).map constantCoeff
  set R := elts.filter fun c ↦ isZ fl (eval0 fl (W + 1) nd.1 c)
  have hroot : ∀ c ∈ R, 1 ≤ rootMultiplicity (S.ev c) q := by
    intro c hc
    have hz := (List.mem_filter.mp hc).2
    rw [S.isZ_iff, S.ev_eval0 (L := (m + 1) * (W + 1)) (by positivity)] at hz
    exact (rootMultiplicity_pos hv.1).mpr hz
  have hRnd : (R.map S.ev).Nodup := hnd.sublist ((List.filter_sublist).map _)
  have hsum : (R.map fun c ↦ rootMultiplicity (S.ev c) q).sum ≤ S.nodeD m W nd := by
    have := RR.sum_rootMultiplicity_le hv.1 hRnd
    rwa [List.map_map] at this
  refine ⟨fun ch hch ↦ ?_, ?_, ?_⟩
  · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hch
    exact (S.childNode_valid hv hℓ c).1
  · rw [List.length_map, length_eq_sum_map_one]
    exact (List.sum_le_sum hroot).trans hsum
  · rw [List.map_map]
    exact (List.sum_le_sum fun c _ ↦ (S.childNode_valid hv hℓ c).2).trans hsum

/-- The invariant of a level: all nodes valid, degrees at `X = 0` summing to at most `W`. -/
def LevelInv (m W ℓ : ℕ) (fr : List Node) : Prop :=
  (∀ nd ∈ fr, S.Valid m W ℓ nd) ∧ (fr.map (S.nodeD m W)).sum ≤ W

/-- **One level.** The truncation drops nothing, and the invariant carries over. -/
theorem level_spec {elts : List (List ℕ)} (hnd : (elts.map S.ev).Nodup) {m W ℓ : ℕ}
    {fr : List Node} (hfr : S.LevelInv m W ℓ fr) (hℓ : ℓ < m) :
    level fl elts m (W + 1) ((m + 1) * (W + 1)) (W + 1) fr =
        fr.flatMap (children fl elts m (W + 1) ((m + 1) * (W + 1))) ∧
      S.LevelInv m W (ℓ + 1) (fr.flatMap (children fl elts m (W + 1) ((m + 1) * (W + 1)))) := by
  have hch := fun nd (h : nd ∈ fr) ↦ S.children_spec hnd (hfr.1 nd h) hℓ
  have hsum : ((fr.flatMap (children fl elts m (W + 1) ((m + 1) * (W + 1)))).map
      (S.nodeD m W)).sum ≤ W := by
    rw [sum_map_flatMap]
    exact (List.sum_le_sum fun nd h ↦ (hch nd h).2.2).trans hfr.2
  refine ⟨List.take_of_length_le ?_, fun ch h ↦ ?_, hsum⟩
  · rw [List.length_flatMap]
    exact (List.sum_le_sum fun nd h ↦ (hch nd h).2.1).trans (hfr.2.trans (Nat.le_succ W))
  · obtain ⟨nd, hnd', hch'⟩ := List.mem_flatMap.mp h
    exact (hch nd hnd').1 ch hch'

/-! ### The levels -/

/-- The frontier after `ℓ` levels. -/
def frontier (elts : List (List ℕ)) (m W : ℕ) (Q : List (List (List ℕ))) (ℓ : ℕ) : List Node :=
  (fun fr ↦ level fl elts m (W + 1) ((m + 1) * (W + 1)) (W + 1) fr)^[ℓ]
    [(stripL fl (W + 1) ((m + 1) * (W + 1)) Q, [])]

omit [Field F] in
theorem rrRoots_eq (elts : List (List ℕ)) (m W : ℕ) (Q : List (List (List ℕ))) :
    rrRoots fl elts m W Q = (frontier (fl := fl) elts m W Q m).map Prod.snd := by
  rw [rrRoots, foldl_range_eq_iterate]
  rfl

omit [Field F] in
theorem frontier_succ (elts : List (List ℕ)) (m W : ℕ) (Q : List (List (List ℕ))) (ℓ : ℕ) :
    frontier (fl := fl) elts m W Q (ℓ + 1) =
      level fl elts m (W + 1) ((m + 1) * (W + 1)) (W + 1) (frontier (fl := fl) elts m W Q ℓ) :=
  Function.iterate_succ_apply' _ _ _

omit [Field F] in
/-- The nodes of level `ℓ ≤ m` carry `ℓ` coefficients. -/
theorem length_of_mem_frontier (elts : List (List ℕ)) (m W : ℕ) (Q : List (List (List ℕ)))
    (ℓ : ℕ) (hℓ : ℓ ≤ m) : ∀ nd ∈ frontier (fl := fl) elts m W Q ℓ, nd.2.length = ℓ := by
  induction ℓ with
  | zero =>
    intro nd h
    simp only [frontier, Function.iterate_zero, id_eq, List.mem_singleton] at h
    rw [h]
    rfl
  | succ ℓ ih =>
    intro nd h
    rw [frontier_succ, level] at h
    obtain ⟨nd', h', hc⟩ := List.mem_flatMap.mp (List.mem_of_mem_take h)
    rw [children_eq] at hc
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hc
    have hl := ih (by omega) nd' h'
    rw [childNode_length W (by omega), hl]

/-- The initial node is valid. -/
theorem levelInv_zero (elts : List (List ℕ)) {m W : ℕ} {Q : List (List (List ℕ))}
    (hQ : S.toBP (W + 1) ((m + 1) * (W + 1)) Q ≠ 0)
    (hdeg : ∀ j, ((S.toBP (W + 1) ((m + 1) * (W + 1)) Q).coeff j).natDegree ≤ W) :
    S.LevelInv m W 0 (frontier (fl := fl) elts m W Q 0) := by
  obtain ⟨v, hv, hne⟩ := S.toBP_stripL _ hQ
  set Q₀ := S.toBP (W + 1) ((m + 1) * (W + 1)) (stripL fl (W + 1) ((m + 1) * (W + 1)) Q)
  refine ⟨fun nd h ↦ ?_, ?_⟩
  · simp only [frontier, Function.iterate_zero, id_eq, List.mem_singleton] at h
    subst h
    refine ⟨hne, fun j ↦ ?_⟩
    rw [zero_mul, add_zero]
    refine le_trans ?_ (hdeg j)
    change (Q₀.coeff j).natDegree ≤ _
    rw [hv, coeff_C_mul]
    rcases eq_or_ne (Q₀.coeff j) 0 with h0 | h0
    · rw [h0, natDegree_zero]
      exact Nat.zero_le _
    · rw [natDegree_X_pow_mul _ h0]
      exact Nat.le_add_right _ _
  · simp only [frontier, Function.iterate_zero, id_eq, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    exact S.nodeD_le m W _

/-- The invariant holds at every level `ℓ ≤ m`, and no level is truncated. -/
theorem levelInv_frontier {elts : List (List ℕ)} (hnd : (elts.map S.ev).Nodup) {m W : ℕ}
    {Q : List (List (List ℕ))} (hQ : S.toBP (W + 1) ((m + 1) * (W + 1)) Q ≠ 0)
    (hdeg : ∀ j, ((S.toBP (W + 1) ((m + 1) * (W + 1)) Q).coeff j).natDegree ≤ W) :
    ∀ ℓ ≤ m, S.LevelInv m W ℓ (frontier (fl := fl) elts m W Q ℓ) := by
  intro ℓ hℓ
  induction ℓ with
  | zero => exact S.levelInv_zero elts hQ hdeg
  | succ ℓ ih =>
    have h := S.level_spec hnd (ih (by omega)) (by omega)
    rw [frontier_succ, h.1]
    exact h.2

/-! ### Completeness -/

private theorem coeff_iterate_divX (p : F[X]) (ℓ i : ℕ) :
    (divX^[ℓ] p).coeff i = p.coeff (i + ℓ) := by
  induction ℓ generalizing i with
  | zero => rfl
  | succ ℓ ih => rw [Function.iterate_succ_apply', coeff_divX, ih]; ring_nf

/-- The node of level `ℓ` on the path of `p`. -/
def OnPath (m W ℓ : ℕ) (p : F[X]) (nd : Node) : Prop :=
  nd.2.length = ℓ ∧ (∀ i < ℓ, S.ev (nd.2.getD i []) = p.coeff i) ∧
    (S.nodeP m W nd).eval (divX^[ℓ] p) = 0

/-- **The path of a root.** A valid node of level `ℓ < m` on the path of `p` has a child on the
path of `p`. -/
theorem exists_child_onPath {elts : List (List ℕ)} (he : ∀ x : F, ∃ c ∈ elts, S.ev c = x)
    {m W ℓ : ℕ} {p : F[X]} {nd : Node} (hv : S.Valid m W ℓ nd) (hℓ : ℓ < m)
    (hp : S.OnPath m W ℓ p nd) :
    ∃ ch ∈ children fl elts m (W + 1) ((m + 1) * (W + 1)) nd, S.OnPath m W (ℓ + 1) p ch := by
  obtain ⟨c, hc, hcv⟩ := he ((divX^[ℓ] p).coeff 0)
  have hroot : isZ fl (eval0 fl (W + 1) nd.1 c) = true := by
    rw [S.isZ_iff, S.ev_eval0 (L := (m + 1) * (W + 1)) (by positivity), hcv]
    change ((S.nodeP m W nd).map constantCoeff).eval _ = 0
    rw [RR.eval_map_constantCoeff, hp.2.2, coeff_zero]
  refine ⟨childNode (fl := fl) m W nd c, ?_, ?_⟩
  · rw [children_eq]
    exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, hroot⟩, rfl⟩
  have hlen := hp.1
  refine ⟨by rw [childNode_length W (by omega), hp.1], fun i hi ↦ ?_, ?_⟩
  · rw [S.ev_getD_childNode m W nd c (by omega) (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hi' : i < nd.2.length := by rw [hp.1]; exact hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
      rw [← List.getD_eq_getElem?_getD]
      exact hp.2.1 i hi
    · have h := hp.1
      simp only [List.getD_eq_getElem?_getD, ← h, List.getElem?_concat_length, Option.getD_some]
      rw [hcv, coeff_iterate_divX, zero_add, h]
  · obtain ⟨v, hv', -⟩ := S.childNode_spec hv hℓ c
    have h := RR.child_eval_divX (S.nodeP m W nd) (divX^[ℓ] p)
    rw [hp.2.2, ← hcv, hv', eval_mul, eval_C, mul_eq_zero] at h
    rw [Function.iterate_succ_apply']
    exact h.resolve_left (pow_ne_zero _ X_ne_zero)

/-- **Completeness of Roth–Ruckenstein.** If `elts` lists every field element exactly once and
the initial polynomial is nonzero, has `X`-degrees at most `W`, and vanishes at `Y = p(X)`, then
some candidate starts with the first `m` coefficients of `p`. -/
theorem rrRoots_complete {elts : List (List ℕ)} (he : ∀ x : F, ∃ c ∈ elts, S.ev c = x)
    (hnd : (elts.map S.ev).Nodup) {m W : ℕ} {Q : List (List (List ℕ))}
    (hQ : S.toBP (W + 1) ((m + 1) * (W + 1)) Q ≠ 0)
    (hdeg : ∀ j, ((S.toBP (W + 1) ((m + 1) * (W + 1)) Q).coeff j).natDegree ≤ W) {p : F[X]}
    (hp : (S.toBP (W + 1) ((m + 1) * (W + 1)) Q).eval p = 0) :
    ∃ pre ∈ rrRoots fl elts m W Q, ∀ i < m, S.ev (pre.getD i []) = p.coeff i := by
  have hpath : ∀ ℓ ≤ m, ∃ nd ∈ frontier (fl := fl) elts m W Q ℓ, S.OnPath m W ℓ p nd := by
    intro ℓ hℓ
    induction ℓ with
    | zero =>
      refine ⟨_, List.mem_singleton_self _, rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _), ?_⟩
      obtain ⟨v, hv, -⟩ := S.toBP_stripL _ hQ
      rw [hv, eval_mul, eval_C, mul_eq_zero] at hp
      exact hp.resolve_left (pow_ne_zero _ X_ne_zero)
    | succ ℓ ih =>
      obtain ⟨nd, hnd', hpath⟩ := ih (by omega)
      have hinv := S.levelInv_frontier hnd hQ hdeg ℓ (by omega)
      obtain ⟨ch, hch, hpath'⟩ :=
        S.exists_child_onPath he (hinv.1 nd hnd') (by omega) hpath
      refine ⟨ch, ?_, hpath'⟩
      rw [frontier_succ, (S.level_spec hnd hinv (by omega)).1]
      exact List.mem_flatMap.mpr ⟨nd, hnd', hch⟩
  obtain ⟨nd, hnd', hpath⟩ := hpath m le_rfl
  exact ⟨nd.2, by rw [rrRoots_eq]; exact List.mem_map_of_mem hnd', hpath.2.1⟩

omit [Field F] in
/-- Every candidate has `m` coefficients. -/
theorem length_of_mem_rrRoots (elts : List (List ℕ)) (m W : ℕ) (Q : List (List (List ℕ))) :
    ∀ pre ∈ rrRoots fl elts m W Q, pre.length = m := by
  intro pre h
  rw [rrRoots_eq] at h
  obtain ⟨nd, hnd, rfl⟩ := List.mem_map.mp h
  exact length_of_mem_frontier elts m W Q m le_rfl nd hnd

end Sem

end BHJK25.RS.DecodeAux
