module

public import BKS23.RandomCut
public import Background.Pruning

/-!
# Cleanup

[BKS23, `lem:clique-intersection`, `lem:sets-pinex`, and the pruning of the proof of Theorem 5.6].
The pruning, Corrádi's bound on the list and the clique intersection are in
`Background/Pruning.lean`, exported here as `BKS23.Cleanup.*`.
-/

@[expose] public section

namespace BKS23.Cleanup

export Pruning (pruneAux prune mem_pruneAux_of_mem mem_of_mem_pruneAux pairwise_pruneAux
  mem_pruneAux mem_prune mem_of_mem_prune pairwise_prune pruneAux_map card_mul_le_corradi
  card_le_of_inter_le card_inter_lt cleanup isNClique_of_mem_cleanup mem_cleanup length_cleanup_le)

end BKS23.Cleanup
