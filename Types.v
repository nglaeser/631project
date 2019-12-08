From Coq Require Import MSets Arith List.
From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Lists.List.
Import ListNotations.
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

Instance showFSet : Show FSet.t :=
  {| show s := show (FSet.elements s) 
  |}.
Compute (show (FSet.add 1 FSet.empty)).


(* straight from QC.v *)
Fixpoint genListSized {A} (sz : nat) (g : G A) : G (list A) :=
  match sz with
    | O => ret nil
    | S sz' =>
        freq [ (1, ret nil) ;
               (sz, liftM2 cons g (genListSized sz' g))
             ]
  end.

(*attempt 1 at a sized generator for lists of nats < n : 
 responds [Warning: The following logical axioms were encountered...] *) 
(*generates lists of length up to len, w elts that are nats < n*)
Definition genNatListSized (n : nat) (len : nat) : G (list nat) :=
  genListSized len (choose (0,n)).
Check genNatListSized.
Sample (genNatListSized 5 2).

(*attempt 2:
 still responds [Warning: The following logical axioms were encountered...] *) 
Fixpoint genNatListSized' (n : nat) (len : nat) : G (list nat) :=
  match len with
    | O => ret nil
    | S len' =>
        freq [ (1, ret nil) ;
               (len, liftM2 cons (choose (0,n)) (genNatListSized n len'))
             ]
  end.
Sample (genNatListSized' 5 2).

(* basically [fold] from Poly.v*)
Fixpoint FSetFold (f: nat->FSet.t->FSet.t) (l: list nat) (b: FSet.t)
                         : FSet.t :=
  match l with
  | nil => b
  | h :: t => f h (FSetFold f t b)
  end.
Check FSetFold.
Check FSet.add.
Compute (show (FSetFold FSet.add [1;2;3] FSet.empty)).

(* function converting a list of nats to an FSet *)
Fixpoint listNatToFSet (l : list nat) : FSet.t :=
  FSetFold FSet.add l FSet.empty.

(* generator for FSets, takes *)
Fixpoint genFSet (n : nat) (len : nat) : G FSet.t :=
  liftM listNatToFSet (genListSized len (choose (0,n))).
Check genFSet.
Check (genFSet 5 2).

Sample (genFSet 5 2).

(* result: Signature mismatch:
       ...
       The value `eq_dec' is required but not provided... *)

(* next TODO: take generator g for FSets and plug in below*) 
Fixpoint genFSys (n : nat) (sys_sz : nat) : G FSys.t :=
  match sys_sz with
  | 0 => ret FSet.empty
  | S sys_sz' =>
    freq [ (1, ret FSet.empty);
             (sys_sz, liftM2 FSys.union (*g*) (genFSys sys_sz' (*g*)))
               ]

(****************************************************************)

(* properties to test *)
Definition q3 (f1 f2 f3 : FSet.t) (F : FSys.t) (n : nat) : bool :=
  (FSys.mem f1 F) && (FSys.mem f2 F) && (FSys.mem f3 F) &&
  negb  (FSet.subset (all_nodes n) (FSet.union (FSet.union f1 f2) f3)).

(* maybe this should be rewritten with Props instead of bools? *)
Definition q3all (F : FSys.t) (n : nat) :=
  forall f1 f2 f3
  

        
