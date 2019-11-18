From Coq Require Import MSets Arith.


(****************************************************************)

(* set of nats between 1 and n (representing nodes), no repeats *)
Module FSet := Make Nat_as_OT.

(* useful operations
- FSet.empty : the empty set
- FSet.is_empty s
- FSet.add x s : insert an element
- union s1 s2
- subset s1 s2 : returns true if s1 <= s2
- mem : membership
 *)

Fixpoint all_nodes (n: nat) : FSet.t :=
  match n with
  | O => FSet.empty
  | S n' => FSet.add n' (all_nodes n')
  end.

(* Example of a network with 5 nodes *)
Definition nodes5 := all_nodes 5.
Compute FSet.elements nodes5.
(* Returns a list [0, 1, 2, 3, 4] *)

(* some examples from StackOverflow *)
Definition test := FSet.union (FSet.singleton 42)
                           (FSet.empty).

(* membership *)
Compute FSet.mem 0 test.   (* evaluates to `false` *)
Compute FSet.mem 42 test.  (* evaluates to `true`  *)

Compute FSet.is_empty test.     (* evaluates to `false` *)
Compute FSet.is_empty FSet.empty.  (* evaluates to `true` *)

(****************************************************************)

(* set of sets of nodes *)
Module FSys := Make FSet.

(* some examples *)
Definition test2 := FSys.union (FSys.singleton test) (FSys.empty).

Compute FSys.mem test test2. (* evaluates to `true` *)
Compute FSys.subset FSys.empty test2. (* evaluates to `true` *)

(****************************************************************)

(* desirable properties *)
Definition b3 (f1 f2 f3 : FSet.t) (F : FSys.t) (n : nat) : bool :=
  (FSys.mem f1 F) && (FSys.mem f2 F) && (FSys.mem f3 F) &&
  negb  (FSet.subset (all_nodes n) (FSet.union (FSet.union f1 f2) f3)).

(* maybe this should be rewritten with Props instead of bools? *)
