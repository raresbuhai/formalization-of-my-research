module

public import BHSV25.Hard.Formula
public import BHSV25.Hard.Machine
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# Templates of growing precision, in polynomial time

For a design `D` and a constant `a₀`, the reduction `BHSV25.Hard.Design.redA D a₀` maps a graph
`G` on `n` vertices to the blow-up of the template of `D` of precision `a = a₀ + ⌈log₂ n⌉`
(`BHSV25.Hard.Design.prec`), so that the template has `|types| · (2 · 4^a)^r = O(n^{2r})` cells
and its error, of order `2^{-a}`, tends to `0` with `n`. It runs in polynomial time
(`BHSV25.Hard.Design.redA_polytime`): the template is computed from the cell numbers by the
arithmetic of `BHSV25/Hard/Formula.lean`, with the data of the types (groups, densities and
correction) as constant tables of the machine, and `2^a = 2^{a₀} 2^{⌈log₂ n⌉}` in unary.
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Turing.MultiTapeTM ComputableInPolyTime

/-- The bit of the blow-up from the bits `W = 1`, `W = -1` and `T` of the pair of cells and the
bit of the pair of vertices of the input graph. -/
def bitF (wp wn t g : Bool) : Bool := (wp && g) || (!wp && ((wn && (t && !g)) || (!wn && t)))

open Classical in
theorem Template.bitF_eq (Tm : Template) {n : ℕ} (G : SimpleGraph (Fin n))
    (p q : Fin Tm.C × Fin n) :
    bitF (decide (Tm.W p.1 q.1 = 1)) (decide (Tm.W p.1 q.1 = -1)) (Tm.T p.1 q.1)
      (decide (G.Adj p.2 q.2)) = decide (Tm.adj G p q) := by
  unfold bitF Template.adj
  rcases Tm.W_cases p.1 q.1 with h | h | h
  · have hT := Tm.W_neg _ _ h
    simp [h, hT]
  · simp [h]
  · simp [h]

theorem getD_ofFn {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) (d : α) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

namespace Design

variable (D : Design)

/-- The number of types. -/
abbrev nT : ℕ := Fintype.card D.Ty

/-- The numbering of the types. -/
noncomputable abbrev tE : D.Ty ≃ Fin D.nT := Fintype.equivFin D.Ty

/-- The precision of the template for a graph on `n` vertices: `a₀ + ⌈log₂ n⌉`. -/
def prec (a₀ n : ℕ) : ℕ := a₀ + Nat.clog 2 n

/-- The number of cells of the template of precision `a`. -/
def cells (a : ℕ) : ℕ := base a ^ D.r * D.nT

theorem cells_eq (a : ℕ) : D.cells a = Fintype.card (D.Cell a) := D.card_cell_eq a

/-! ### The tables of the types -/

/-- The groups of the types, by number. -/
noncomputable def grTab : List ℕ := List.ofFn fun t : Fin D.nT ↦ (D.gr (D.tE.symm t) : ℕ)

/-- The densities between groups, at `i K + j`. -/
noncomputable def qTab : List ℕ :=
  List.ofFn fun i : Fin (D.K * D.K) ↦ D.q (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- Where the correction between types is `z`, at `t nT + t'`. -/
noncomputable def wTab (z : ℤ) : List Bool :=
  List.ofFn fun i : Fin (D.nT * D.nT) ↦
    decide (D.W0 (D.tE.symm (finProdFinEquiv.symm i).1) (D.tE.symm (finProdFinEquiv.symm i).2) = z)

theorem grTab_getD (τ : D.Ty) : D.grTab.getD (D.tE τ) 0 = (D.gr τ : ℕ) := by
  rw [grTab, getD_ofFn, Equiv.symm_apply_apply]

theorem qTab_getD (i j : Fin D.K) : D.qTab.getD (i * D.K + j) 0 = D.q i j := by
  have h : (i : ℕ) * D.K + j = (finProdFinEquiv (i, j) : ℕ) := by
    rw [finProdFinEquiv_apply_val]; ring
  rw [qTab, h, getD_ofFn, Equiv.symm_apply_apply]

theorem wTab_getD (z : ℤ) (τ τ' : D.Ty) :
    (D.wTab z).getD (D.tE τ * D.nT + D.tE τ') false = decide (D.W0 τ τ' = z) := by
  have h : ((D.tE τ : ℕ)) * D.nT + D.tE τ' = (finProdFinEquiv (D.tE τ, D.tE τ') : ℕ) := by
    rw [finProdFinEquiv_apply_val]; ring
  rw [wTab, h, getD_ofFn, Equiv.symm_apply_apply]
  simp

/-! ### The bits of the template -/

/-- The adjacency of the cells numbered `u, u'` in the template of precision `a`. -/
noncomputable def tBit (a u u' : ℕ) : Bool :=
  decide (D.grTab.getD (u % D.nT) 0 ≠ D.grTab.getD (u' % D.nT) 0) &&
    decide (hvalN a D.r (u / D.nT) (u' / D.nT) <
      D.qTab.getD (D.grTab.getD (u % D.nT) 0 * D.K + D.grTab.getD (u' % D.nT) 0) 0)

/-- Whether the correction between the cells numbered `u, u'` is `z`, for `z = ±1`. -/
noncomputable def wBit (z : ℤ) (u u' : ℕ) : Bool :=
  decide (u / D.nT = u' / D.nT) && (D.wTab z).getD (u % D.nT * D.nT + u' % D.nT) false

theorem tE_eqv_symm (a : ℕ) (u : Fin (Fintype.card (D.Cell a))) :
    (u : ℕ) % D.nT = D.tE ((D.eqv a).symm u).1 := (D.eqv_symm_fst a u).symm

theorem T_eq_tBit (a : ℕ) (u u' : Fin (Fintype.card (D.Cell a))) :
    (D.template a).T u u' = D.tBit a u u' := by
  rw [T_eq, tBit, D.tE_eqv_symm a u, D.tE_eqv_symm a u', grTab_getD, grTab_getD, qTab_getD]
  congr 1

theorem W_eq_wBit (a : ℕ) (u u' : Fin (Fintype.card (D.Cell a))) {z : ℤ} (hz : z ≠ 0) :
    decide ((D.template a).W u u' = z) = D.wBit z u u' := by
  rw [W_eq, wBit, D.tE_eqv_symm a u, D.tE_eqv_symm a u', wTab_getD]
  split_ifs with h <;> simp [h, Ne.symm hz]

/-! ### The reduction -/

/-- **The reduction**: the blow-up of `G` by the template of precision `a₀ + ⌈log₂ n⌉`. -/
noncomputable def redA (a₀ : ℕ) (G : Graph) : Graph := (D.template (prec a₀ G.1)).blowup G

/-- The number of vertices of the blow-up of a graph on `n` vertices. -/
def nA (a₀ n : ℕ) : ℕ := D.cells (prec a₀ n) * n

/-- The bit of the adjacency table of the blow-up at the pair index `P`. -/
noncomputable def bitAt (a₀ n : ℕ) (tbl : List Bool) (P : ℕ) : Bool :=
  bitF (D.wBit 1 (P / D.nA a₀ n / n) (P % D.nA a₀ n / n))
    (D.wBit (-1) (P / D.nA a₀ n / n) (P % D.nA a₀ n / n))
    (D.tBit (prec a₀ n) (P / D.nA a₀ n / n) (P % D.nA a₀ n / n))
    (tbl.getD (P / D.nA a₀ n % n * n + P % D.nA a₀ n % n) false)

/-- The adjacency table of the blow-up, on lists. -/
noncomputable def tableA (a₀ n : ℕ) (tbl : List Bool) : List Bool :=
  (List.range (D.nA a₀ n * D.nA a₀ n)).map (D.bitAt a₀ n tbl)

theorem redA_fst (a₀ : ℕ) (G : Graph) : (D.redA a₀ G).1 = D.nA a₀ G.1 := by
  simp [redA, nA, cells_eq]

theorem tableA_eq (a₀ : ℕ) (G : Graph) : D.tableA a₀ G.1 (adjTable G) = adjTable (D.redA a₀ G) := by
  classical
  set Tm := D.template (prec a₀ G.1)
  have hN : D.nA a₀ G.1 = Tm.C * G.1 := by simp [nA, cells_eq, Tm]
  unfold tableA
  apply List.ext_getElem (by simp [adjTable, redA, hN, Tm])
  intro P h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [adjTable_getElem]
  obtain ⟨e1, e2⟩ := finProdFinEquiv_symm_val
    (⟨P, by simpa [adjTable] using h2⟩ : Fin ((D.redA a₀ G).1 * (D.redA a₀ G).1))
  set p := (finProdFinEquiv.symm
    (⟨P, by simpa [adjTable] using h2⟩ : Fin ((D.redA a₀ G).1 * (D.redA a₀ G).1))).1
  set q := (finProdFinEquiv.symm
    (⟨P, by simpa [adjTable] using h2⟩ : Fin ((D.redA a₀ G).1 * (D.redA a₀ G).1))).2
  have hred : (D.redA a₀ G).1 = D.nA a₀ G.1 := D.redA_fst a₀ G
  have e1' : (p : ℕ) = P / D.nA a₀ G.1 := by rw [e1, Fin.val_mk, hred]
  have e2' : (q : ℕ) = P % D.nA a₀ G.1 := by rw [e2, Fin.val_mk, hred]
  rw [show decide ((D.redA a₀ G).2.Adj p q) =
    decide (Tm.adj G.2 (finProdFinEquiv.symm p) (finProdFinEquiv.symm q)) from rfl]
  rw [← Tm.bitF_eq G.2, ← adjTable_getD]
  obtain ⟨f1, f2⟩ := finProdFinEquiv_symm_val p
  obtain ⟨f3, f4⟩ := finProdFinEquiv_symm_val q
  rw [D.W_eq_wBit _ _ _ one_ne_zero, D.W_eq_wBit _ _ _ (by norm_num), D.T_eq_tBit]
  unfold bitAt
  rw [f1, f2, f3, f4, e1', e2']

/-! ### Polynomial time -/

section Machine

variable {γ : Type} {input : γ ↪ List Bool} {a₀ : ℕ} {n : γ → ℕ}

theorem prec_polytime (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun z ↦ prec a₀ (n z)) input encUnary :=
  unary_add' (const a₀) ((unary_clog_const 2).comp hn)

/-- `2^a` for `a = a₀ + ⌈log₂ n⌉`, in unary. -/
theorem pa_polytime (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun z ↦ 2 ^ prec a₀ (n z)) input encUnary := by
  have e : (fun z ↦ 2 ^ prec a₀ (n z)) = fun z ↦ 2 ^ a₀ * 2 ^ Nat.clog 2 (n z) :=
    funext fun z ↦ by simp [prec, pow_add]
  rw [e]
  exact unary_mul' (const _) (unary_pow_clog_const hn 2 2)

theorem pp_polytime (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun z ↦ 2 ^ prec a₀ (n z) * 2 ^ prec a₀ (n z)) input encUnary :=
  unary_mul' (pa_polytime hn) (pa_polytime hn)

theorem base_polytime (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun z ↦ base (prec a₀ (n z))) input encUnary :=
  unary_mul' (const 2) (pp_polytime hn)

theorem cells_polytime (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun z ↦ D.cells (prec a₀ (n z))) input encUnary :=
  unary_mul' ((unary_pow D.r).comp (base_polytime hn)) (const D.nT)

theorem dig_polytime (hn : ComputableInPolyTime n input encUnary) (l : ℕ) {x : γ → ℕ}
    (hx : ComputableInPolyTime x input encUnary) :
    ComputableInPolyTime (fun z ↦ dig (prec a₀ (n z)) l (x z)) input encUnary :=
  unary_mod.comp ((unary_div.comp (hx.prod ((unary_pow l).comp (base_polytime hn)))).prod
    (base_polytime hn))

theorem bentN_polytime (hn : ComputableInPolyTime n input encUnary) {g g' : γ → ℕ}
    (hg : ComputableInPolyTime g input encUnary) (hg' : ComputableInPolyTime g' input encUnary) :
    ComputableInPolyTime (fun z ↦ bentN (prec a₀ (n z)) (g z) (g' z)) input encUnary := by
  have hpp := pp_polytime (a₀ := a₀) hn
  have hpa := pa_polytime (a₀ := a₀) hn
  have hB : ∀ {h : γ → ℕ}, ComputableInPolyTime h input encUnary →
      ComputableInPolyTime (fun z ↦ dB (prec a₀ (n z)) (h z)) input encUnary :=
    fun hh ↦ unary_div.comp (hh.prod hpp)
  have hX : ∀ {h : γ → ℕ}, ComputableInPolyTime h input encUnary →
      ComputableInPolyTime (fun z ↦ dX (prec a₀ (n z)) (h z)) input encUnary :=
    fun hh ↦ unary_div.comp ((unary_mod.comp (hh.prod hpp)).prod hpa)
  have hY : ∀ {h : γ → ℕ}, ComputableInPolyTime h input encUnary →
      ComputableInPolyTime (fun z ↦ dY (prec a₀ (n z)) (h z)) input encUnary :=
    fun hh ↦ unary_mod.comp ((unary_mod.comp (hh.prod hpp)).prod hpa)
  have hbit : ∀ {h : γ → ℕ}, ComputableInPolyTime h input encUnary →
      ComputableInPolyTime (fun p : γ × ℕ ↦ (h p.1).testBit p.2) (encPair input encUnary)
        encBool := fun hh ↦
    .of_tidy (ComputableTidilyInPolyTime.binary_testBit (toBinary' (hh.comp (fst _ _))).tidy
      (snd _ _).tidy)
  have hne : ∀ {b b' : γ × ℕ → Bool}, ComputableInPolyTime b (encPair input encUnary) encBool →
      ComputableInPolyTime b' (encPair input encUnary) encBool →
      ComputableInPolyTime (fun p ↦ decide (b p ≠ b' p)) (encPair input encUnary) encBool := by
    intro b b' hb hb'
    have e : (fun p ↦ decide (b p ≠ b' p)) = fun p ↦ !decide (b p = b' p) :=
      funext fun p ↦ by simp
    rw [e]
    exact bool_not.comp (decide_eq' hb hb')
  have htest : ComputableInPolyTime (fun p : γ × ℕ ↦ decide
      ((dX (prec a₀ (n p.1)) (g p.1)).testBit p.2 ≠ (dX (prec a₀ (n p.1)) (g' p.1)).testBit p.2 ∧
        (dY (prec a₀ (n p.1)) (g p.1)).testBit p.2 ≠ (dY (prec a₀ (n p.1)) (g' p.1)).testBit p.2))
      (encPair input encUnary) encBool := by
    have e : (fun p : γ × ℕ ↦ decide
        ((dX (prec a₀ (n p.1)) (g p.1)).testBit p.2 ≠ (dX (prec a₀ (n p.1)) (g' p.1)).testBit p.2 ∧
          (dY (prec a₀ (n p.1)) (g p.1)).testBit p.2 ≠
            (dY (prec a₀ (n p.1)) (g' p.1)).testBit p.2)) =
        fun p ↦ decide ((dX (prec a₀ (n p.1)) (g p.1)).testBit p.2 ≠
          (dX (prec a₀ (n p.1)) (g' p.1)).testBit p.2) &&
          decide ((dY (prec a₀ (n p.1)) (g p.1)).testBit p.2 ≠
            (dY (prec a₀ (n p.1)) (g' p.1)).testBit p.2) :=
      funext fun p ↦ Bool.decide_and _ _
    rw [e]
    exact bool_and' (hne (hbit (hX hg)) (hbit (hX hg'))) (hne (hbit (hY hg)) (hbit (hY hg')))
  have hcount := countPWithInput (list := fun z ↦ List.range (prec a₀ (n z)))
    (test := fun z i ↦ decide
      ((dX (prec a₀ (n z)) (g z)).testBit i ≠ (dX (prec a₀ (n z)) (g' z)).testBit i ∧
        (dY (prec a₀ (n z)) (g z)).testBit i ≠ (dY (prec a₀ (n z)) (g' z)).testBit i))
    (unary_range' (prec_polytime hn)) htest
  have hif : ComputableInPolyTime (fun z ↦ if dB (prec a₀ (n z)) (g z) = dB (prec a₀ (n z)) (g' z)
      then 0 else 1) input encUnary := by
    have e : (fun z ↦ if dB (prec a₀ (n z)) (g z) = dB (prec a₀ (n z)) (g' z) then 0 else 1) =
        fun z ↦ if decide (dB (prec a₀ (n z)) (g z) = dB (prec a₀ (n z)) (g' z)) then 0 else 1 :=
      funext fun z ↦ by simp
    rw [e]
    exact ite' (decide_eq' (hB hg) (hB hg')) (const 0) (const 1)
  exact unary_mod.comp ((unary_add' hif hcount).prod (const 2))

theorem hvalN_polytime (hn : ComputableInPolyTime n input encUnary) {x x' : γ → ℕ}
    (hx : ComputableInPolyTime x input encUnary) (hx' : ComputableInPolyTime x' input encUnary) :
    ∀ r : ℕ, ComputableInPolyTime (fun z ↦ hvalN (prec a₀ (n z)) r (x z) (x' z)) input encUnary
  | 0 => by
    have e : (fun z ↦ hvalN (prec a₀ (n z)) 0 (x z) (x' z)) = fun _ ↦ 0 :=
      funext fun z ↦ by simp [hvalN]
    rw [e]
    exact const 0
  | r + 1 => by
    have e : (fun z ↦ hvalN (prec a₀ (n z)) (r + 1) (x z) (x' z)) = fun z ↦
        hvalN (prec a₀ (n z)) r (x z) (x' z) + bentN (prec a₀ (n z))
          (dig (prec a₀ (n z)) r (x z)) (dig (prec a₀ (n z)) r (x' z)) * 2 ^ r :=
      funext fun z ↦ by simp [hvalN, List.range_succ]
    rw [e]
    exact unary_add' (hvalN_polytime hn hx hx' r)
      (unary_mul' (bentN_polytime hn (dig_polytime hn r hx) (dig_polytime hn r hx')) (const _))

theorem tBit_polytime (hn : ComputableInPolyTime n input encUnary) {u u' : γ → ℕ}
    (hu : ComputableInPolyTime u input encUnary) (hu' : ComputableInPolyTime u' input encUnary) :
    ComputableInPolyTime (fun z ↦ D.tBit (prec a₀ (n z)) (u z) (u' z)) input encBool := by
  have hgr : ComputableInPolyTime (fun _ : γ ↦ D.grTab) input (encList encUnary) := const _
  have hqt : ComputableInPolyTime (fun _ : γ ↦ D.qTab) input (encList encUnary) := const _
  have ht := unary_mod.comp (hu.prod (const D.nT))
  have ht' := unary_mod.comp (hu'.prod (const D.nT))
  have hs := unary_div.comp (hu.prod (const D.nT))
  have hs' := unary_div.comp (hu'.prod (const D.nT))
  have hg := listGetDWithInput hgr ht 0
  have hg' := listGetDWithInput hgr ht' 0
  have hq := listGetDWithInput hqt (unary_add' (unary_mul' hg (const D.K)) hg') 0
  have hh := hvalN_polytime (a₀ := a₀) hn hs hs' D.r
  have e : (fun z ↦ D.tBit (prec a₀ (n z)) (u z) (u' z)) = fun z ↦
      !decide (D.grTab.getD (u z % D.nT) 0 = D.grTab.getD (u' z % D.nT) 0) &&
        decide (hvalN (prec a₀ (n z)) D.r (u z / D.nT) (u' z / D.nT) <
          D.qTab.getD (D.grTab.getD (u z % D.nT) 0 * D.K + D.grTab.getD (u' z % D.nT) 0) 0) :=
    funext fun z ↦ by simp [tBit]
  rw [e]
  exact bool_and' (bool_not.comp (decide_eq' hg hg')) (unary_lt' hh hq)

theorem wBit_polytime (w : ℤ) {u u' : γ → ℕ} (hu : ComputableInPolyTime u input encUnary)
    (hu' : ComputableInPolyTime u' input encUnary) :
    ComputableInPolyTime (fun z ↦ D.wBit w (u z) (u' z)) input encBool := by
  have hs := unary_div.comp (hu.prod (const D.nT))
  have hs' := unary_div.comp (hu'.prod (const D.nT))
  have ht := unary_mod.comp (hu.prod (const D.nT))
  have ht' := unary_mod.comp (hu'.prod (const D.nT))
  have hw : ComputableInPolyTime (fun _ : γ ↦ D.wTab w) input encBits := const _
  exact bool_and' (decide_eq' hs hs')
    (bitsGetDWithInput hw (unary_add' (unary_mul' ht (const D.nT)) ht') false)

theorem bitAt_polytime (a₀ : ℕ) :
    ComputableInPolyTime (fun z : (ℕ × List Bool) × ℕ ↦ D.bitAt a₀ (Template.nG z.1) z.1.2 z.2)
      (encPair (encPair encNat encBits) encUnary) encBool := by
  have hn := Template.nG_polytime.comp (fst (encPair encNat encBits) encUnary)
  have htbl := (snd encNat encBits).comp (fst (encPair encNat encBits) encUnary)
  have hP := snd (encPair encNat encBits) encUnary
  have hN := unary_mul' (D.cells_polytime (a₀ := a₀) hn) hn
  have hp := unary_div.comp (hP.prod hN)
  have hq := unary_mod.comp (hP.prod hN)
  have hu := unary_div.comp (hp.prod hn)
  have hu' := unary_div.comp (hq.prod hn)
  have hv := unary_mod.comp (hp.prod hn)
  have hv' := unary_mod.comp (hq.prod hn)
  have hg := bitsGetDWithInput htbl (unary_add' (unary_mul' hv hn) hv') false
  have hwp := D.wBit_polytime 1 hu hu'
  have hwn := D.wBit_polytime (-1) hu hu'
  have ht := D.tBit_polytime (a₀ := a₀) hn hu hu'
  unfold bitAt bitF
  exact bool_or.comp ((bool_and' hwp hg).prod (bool_and' (bool_not.comp hwp)
    (bool_or.comp ((bool_and' hwn (bool_and' ht (bool_not.comp hg))).prod
      (bool_and' (bool_not.comp hwn) ht)))))

/-- The output of the machine: the number of vertices and the adjacency table. -/
noncomputable def redOutA (a₀ : ℕ) (x : ℕ × List Bool) : ℕ × List Bool :=
  (D.cells (prec a₀ (Template.nG x)) * x.1, D.tableA a₀ (Template.nG x) x.2)

theorem encGraph_redA (a₀ : ℕ) (G : Graph) :
    encGraph (D.redA a₀ G) = encPair encNat encBits (D.redOutA a₀ (G.1, adjTable G)) := by
  have hn : Template.nG (G.1, adjTable G) = G.1 := by
    unfold Template.nG
    simp only
    rw [length_adjTable, min_eq_right (by nlinarith)]
  unfold redOutA
  rw [hn, tableA_eq]
  have h : ((D.redA a₀ G).1, adjTable (D.redA a₀ G)) =
      (D.cells (prec a₀ G.1) * G.1, adjTable (D.redA a₀ G)) := by rw [redA_fst]; rfl
  rw [← h]
  rfl

theorem redOutA_polytime (a₀ : ℕ) :
    ComputableInPolyTime (D.redOutA a₀) (encPair encNat encBits) (encPair encNat encBits) := by
  have hn := Template.nG_polytime
  have hN := unary_mul' (D.cells_polytime (a₀ := a₀) hn) hn
  have hmap := mapWithInput (list := fun x : ℕ × List Bool ↦
      List.range (D.nA a₀ (Template.nG x) * D.nA a₀ (Template.nG x)))
    (f := fun x P ↦ D.bitAt a₀ (Template.nG x) x.2 P) (unary_range' (unary_mul' hN hN))
    (D.bitAt_polytime a₀)
  exact (binary_mul' (toBinary' (D.cells_polytime hn)) (fst _ _)).prod (listToBits.comp hmap)

/-- **The reduction runs in polynomial time.** -/
theorem redA_polytime (a₀ : ℕ) : ComputableInPolyTime (D.redA a₀) encGraph encGraph :=
  ((D.redOutA_polytime a₀).comp graph_polytime).of_enc_eq (D.encGraph_redA a₀)

end Machine

end Design

end BHSV25.Hard
