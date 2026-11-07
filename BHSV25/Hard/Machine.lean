module

public import BHSV25.Hard.Glue
public import BHSV25.Hard.Blowup

/-!
# Blow-ups are computed in polynomial time

For a fixed template `Tm`, the blow-up `G ↦ Tm.blowup G` (`BHSV25/Hard/Blowup.lean`) runs in
polynomial time (`BHSV25.Hard.Template.blowup_polytime`). The tables of `T` and of the signs of
`W` are constants of the machine (`BHSV25.Hard.Template.tTab`, `.wPos`, `.wNeg`); the bit of the
adjacency table of the blow-up at the pair index `P = p N + q`, `N = C n`, is computed from the
cells `p / n, q / n`, the vertices `p % n, q % n` of `G`, and one bit of the adjacency table of
`G` (`BHSV25.Hard.Template.bitB`, `BHSV25.Hard.Template.tableB_eq`).
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Turing.MultiTapeTM ComputableInPolyTime

/-- Reading a table of a function of two arguments, row by row. -/
theorem ofFn_pair_getD {m m' : ℕ} (f : Fin m → Fin m' → Bool) (u : Fin m) (u' : Fin m') :
    (List.ofFn fun i : Fin (m * m') ↦ f (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm i).2).getD (u * m' + u') false = f u u' := by
  have hlt : (u : ℕ) * m' + u' < m * m' := by
    have := u.2; have := u'.2; nlinarith
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [hlt, ↓reduceDIte, Option.getD_some]
  have hk : (⟨u * m' + u', hlt⟩ : Fin (m * m')) = finProdFinEquiv (u, u') := by
    ext; simp [finProdFinEquiv]; ring
  rw [hk, Equiv.symm_apply_apply]

open Classical in
theorem adjTable_getElem (G : Graph) (P : ℕ) (h : P < (adjTable G).length) :
    (adjTable G)[P] = decide (G.2.Adj
      (finProdFinEquiv.symm (⟨P, by simpa [adjTable] using h⟩ : Fin (G.1 * G.1))).1
      (finProdFinEquiv.symm (⟨P, by simpa [adjTable] using h⟩ : Fin (G.1 * G.1))).2) := by
  simp only [adjTable, List.getElem_ofFn]

theorem finProdFinEquiv_symm_val {m n : ℕ} (i : Fin (m * n)) :
    ((finProdFinEquiv.symm i).1 : ℕ) = i / n ∧ ((finProdFinEquiv.symm i).2 : ℕ) = i % n := by
  simp [finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat]

namespace Template

variable (Tm : Template)

/-- The table of `T`, row by row. -/
def tTab : List Bool :=
  List.ofFn fun i : Fin (Tm.C * Tm.C) ↦ Tm.T (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- The table of `W = 1`. -/
def wPos : List Bool :=
  List.ofFn fun i : Fin (Tm.C * Tm.C) ↦
    decide (Tm.W (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 = 1)

/-- The table of `W = -1`. -/
def wNeg : List Bool :=
  List.ofFn fun i : Fin (Tm.C * Tm.C) ↦
    decide (Tm.W (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 = -1)

/-- The bit of the adjacency table of the blow-up at the pair of cells `i = u C + u'`, given the
bit `g` of the pair of vertices of `G`. -/
def bitOf (i : ℕ) (g : Bool) : Bool :=
  (Tm.wPos.getD i false && g) ||
    (!Tm.wPos.getD i false && ((Tm.wNeg.getD i false && (Tm.tTab.getD i false && !g)) ||
      (!Tm.wNeg.getD i false && Tm.tTab.getD i false)))

/-- The bit of the adjacency table of the blow-up at the pair index `P`. -/
def bitB (n : ℕ) (tbl : List Bool) (P : ℕ) : Bool :=
  Tm.bitOf (P / (Tm.C * n) / n * Tm.C + P % (Tm.C * n) / n)
    (tbl.getD (P / (Tm.C * n) % n * n + P % (Tm.C * n) % n) false)

/-- The adjacency table of the blow-up, on lists. -/
def tableB (n : ℕ) (tbl : List Bool) : List Bool :=
  (List.range ((Tm.C * n) * (Tm.C * n))).map (Tm.bitB n tbl)

open Classical in
theorem bitOf_eq {n : ℕ} (G : SimpleGraph (Fin n)) (p q : Fin Tm.C × Fin n) :
    Tm.bitOf (p.1 * Tm.C + q.1) (decide (G.Adj p.2 q.2)) = decide (Tm.adj G p q) := by
  unfold bitOf tTab wPos wNeg
  rw [ofFn_pair_getD (fun u u' ↦ decide (Tm.W u u' = 1)),
    ofFn_pair_getD (fun u u' ↦ decide (Tm.W u u' = -1)), ofFn_pair_getD Tm.T]
  unfold adj
  rcases Tm.W_cases p.1 q.1 with h | h | h
  · have hT := Tm.W_neg _ _ h
    simp [h, hT]
  · simp [h]
  · simp [h]

open Classical in
theorem decide_adj_blowup (G : Graph) (p q : Fin (Tm.C * G.1)) :
    decide ((Tm.blowup G).2.Adj p q) = Tm.bitOf (p / G.1 * Tm.C + q / G.1)
      ((adjTable G).getD (p % G.1 * G.1 + q % G.1) false) := by
  have h := Tm.bitOf_eq G.2 (finProdFinEquiv.symm p) (finProdFinEquiv.symm q)
  rw [← adjTable_getD] at h
  obtain ⟨e1, e2⟩ := finProdFinEquiv_symm_val p
  obtain ⟨e3, e4⟩ := finProdFinEquiv_symm_val q
  rw [e1, e2, e3, e4] at h
  exact h.symm

theorem tableB_eq (G : Graph) : Tm.tableB G.1 (adjTable G) = adjTable (Tm.blowup G) := by
  classical
  unfold tableB
  apply List.ext_getElem (by simp [adjTable])
  intro P h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [adjTable_getElem, decide_adj_blowup]
  obtain ⟨e1, e2⟩ := finProdFinEquiv_symm_val
    (⟨P, by simpa [adjTable] using h2⟩ : Fin ((Tm.blowup G).1 * (Tm.blowup G).1))
  unfold bitB
  rw [e1, e2]

/-- The output of the blow-up machine: the number of vertices and the adjacency table, with the
number of vertices of `G` capped by the length of its table. -/
def redOut (x : ℕ × List Bool) : ℕ × List Bool :=
  (Tm.C * x.1, Tm.tableB (min (x.2.length + 1) x.1) x.2)

theorem encGraph_blowup (G : Graph) :
    encGraph (Tm.blowup G) = encPair encNat encBits (Tm.redOut (G.1, adjTable G)) := by
  unfold redOut
  simp only
  rw [length_adjTable, min_eq_right (by nlinarith), tableB_eq]
  rfl

/-- The number of vertices, capped by the length of the table, in unary. -/
def nG (x : ℕ × List Bool) : ℕ := min (x.2.length + 1) x.1

omit Tm in
theorem nG_polytime : ComputableInPolyTime nG (encPair encNat encBits) encUnary := by
  have hlen : ComputableInPolyTime (fun x : ℕ × List Bool ↦ x.2.length + 1)
      (encPair encNat encBits) encUnary := unary_succ.comp (length_bits.comp (snd _ _))
  exact binary_min_unary' hlen (fst _ _)

theorem bitB_polytime :
    ComputableInPolyTime (fun z : (ℕ × List Bool) × ℕ ↦ Tm.bitB (nG z.1) z.1.2 z.2)
      (encPair (encPair encNat encBits) encUnary) encBool := by
  have hx := fst (encPair encNat encBits) encUnary
  have hn := nG_polytime.comp hx
  have htbl := (snd encNat encBits).comp hx
  have hP := snd (encPair encNat encBits) encUnary
  have hN := unary_mul' (const Tm.C) hn
  have hp := unary_div.comp (hP.prod hN)
  have hq := unary_mod.comp (hP.prod hN)
  have hu := unary_div.comp (hp.prod hn)
  have hv := unary_mod.comp (hp.prod hn)
  have hu' := unary_div.comp (hq.prod hn)
  have hv' := unary_mod.comp (hq.prod hn)
  have hi := unary_add' (unary_mul' hu (const Tm.C)) hu'
  have hgi := unary_add' (unary_mul' hv hn) hv'
  have hg := bitsGetDWithInput htbl hgi false
  have hwp := bitsGetDWithInput (const Tm.wPos) hi false
  have hwn := bitsGetDWithInput (const Tm.wNeg) hi false
  have ht := bitsGetDWithInput (const Tm.tTab) hi false
  unfold bitB bitOf
  exact bool_or.comp ((bool_and' hwp hg).prod (bool_and' (bool_not.comp hwp)
    (bool_or.comp ((bool_and' hwn (bool_and' ht (bool_not.comp hg))).prod
      (bool_and' (bool_not.comp hwn) ht)))))

theorem redOut_polytime :
    ComputableInPolyTime Tm.redOut (encPair encNat encBits) (encPair encNat encBits) := by
  have hN := unary_mul' (const Tm.C) nG_polytime
  have hmap := mapWithInput (list := fun x : ℕ × List Bool ↦
      List.range ((Tm.C * nG x) * (Tm.C * nG x)))
    (f := fun x P ↦ Tm.bitB (nG x) x.2 P) (unary_range' (unary_mul' hN hN)) Tm.bitB_polytime
  exact (binary_mul' (const Tm.C) (fst _ _)).prod (listToBits.comp hmap)

/-- **The blow-up runs in polynomial time.** -/
theorem blowup_polytime : ComputableInPolyTime Tm.blowup encGraph encGraph :=
  (Tm.redOut_polytime.comp graph_polytime).of_enc_eq Tm.encGraph_blowup

end Template

end BHSV25.Hard
