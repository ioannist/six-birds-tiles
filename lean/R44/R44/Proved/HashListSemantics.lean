/- -- [compile-fix]
# Extensional meaning of the existing hash-list certificates

Source: A-C4.4/A-FS5.2 and the literal predicates in R44/FiniteModel.lean.
This file proves generic container facts; it does not generate or enumerate
any feature mates. In particular, equal hash-set sizes plus inclusion are
converted to equality of ordinary membership predicates.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.LogicalSpineFoundation -- [compile-fix]
import Std.Data.HashSet.Lemmas

namespace R44.DischargeHashLists

section
variable {α : Type} [BEq α] [LawfulBEq α] [Hashable α]
variable [LawfulHashable α] [DecidableEq α]

private theorem mem_hashList (m : Std.HashSet α) (x : α) :
    x ∈ m.toList ↔ x ∈ m := by
  exact Std.HashSet.mem_toList
  -- API?: expected Std.HashSet.mem_toList : x ∈ m.toList ↔ x ∈ m.

private theorem hashList_nodup (m : Std.HashSet α) : m.toList.Nodup := by
  simpa only [List.nodup_iff_pairwise_ne, beq_eq_false_iff_ne] using
    Std.HashSet.distinct_toList (m := m)
  -- API?: expected distinct_toList : List.Pairwise (fun a b => (a == b) = false) m.toList.

private theorem hash_finset_card (m : Std.HashSet α) :
    m.toList.toFinset.card = m.size := by
  rw [List.toFinset_card_of_nodup (hashList_nodup m)]
  exact Std.HashSet.length_toList
  -- API?: expected length_toList : m.toList.length = m.size.

/-- Generic hash/list conversion. Hashing is not used as a proof oracle. -/
theorem hashSetEq_membership {a b : List α} (h : hashSetEq a b = true) :
    ∀ x, x ∈ a ↔ x ∈ b := by
  classical
  let ha := Std.HashSet.ofList a
  let hb := Std.HashSet.ofList b
  have parts : ha.size = hb.size ∧ ∀ x ∈ a, hb.contains x = true := by
    simpa only [hashSetEq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      ha, hb] using h
  have hsub : ha.toList.toFinset ⊆ hb.toList.toFinset := by
    intro x hx
    have hma : x ∈ ha := (mem_hashList ha x).mp (List.mem_toFinset.mp hx)
    have hxa : x ∈ a := by
      simpa [ha, Std.HashSet.mem_ofList] using hma
      -- API?: mem_ofList reduces to List.contains = true; LawfulBEq converts it to membership.
    have hmb : x ∈ hb := (Std.HashSet.contains_iff_mem).mp (parts.2 x hxa)
    exact List.mem_toFinset.mpr ((mem_hashList hb x).mpr hmb)
  have hcard : ha.toList.toFinset.card = hb.toList.toFinset.card := by
    rw [hash_finset_card, hash_finset_card, parts.1]
  have heq : ha.toList.toFinset = hb.toList.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    -- API?: expected Finset.eq_of_subset_of_card_le : s ⊆ t → t.card ≤ s.card → s = t.
  intro x
  have hh : (x ∈ ha.toList.toFinset) ↔ (x ∈ hb.toList.toFinset) :=
    iff_of_eq (congrArg (fun s : Finset α => x ∈ s) heq)
  simpa [ha,hb,List.mem_toFinset,Std.HashSet.mem_toList,
    Std.HashSet.mem_ofList] using hh

/-- Hash deduplication changes order but not the represented set. -/
theorem mem_hashDedup {a : List α} {x : α} : x ∈ hashDedup a ↔ x ∈ a := by
  simp [hashDedup, Std.HashSet.mem_toList, Std.HashSet.mem_ofList]

end
end R44.DischargeHashLists
