From Coq Require Import FSets Arith List. Import ListNotations.
From QuickChick Require Import QuickChick. Import QcNotation.

Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.

Require Import String. Local Open Scope string.
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


Instance showFSet : Show FSet.t :=
  {| show s := show (FSet.elements s) 
  |}.
Compute (show (FSet.add 1 FSet.empty)).

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

(*now to build our generator! first, some familiar helper functions *)

(* straight from QC.v *)
Fixpoint genListSized {A} (sz : nat) (g : G A) : G (list A) :=
  match sz with
    | O => ret nil
    | S sz' =>
        freq [ (1, ret nil) ;
               ((Nat.square sz), liftM2 cons g (genListSized sz' g))
             ]
  end.

(* the following sometimes responds 
   [Warning: The following logical axioms were encountered...]
   which Leo says not to worry about*) 
(*generates lists of length up to len, w elts that are nats < n*)
Definition genNatListSized (n : nat) (len : nat) : G (list nat) :=
  genListSized len (choose (0,n)).

(* Sample (genNatListSized 5 2).*)

Fixpoint genNatListSized' (n : nat) (len : nat) : G (list nat) :=
  match len with
    | O => ret nil
    | S len' =>
        freq [ (1, ret nil) ;
               (len, liftM2 cons (choose (0,n)) (genNatListSized n len'))
             ]
  end.
(*Sample (genNatListSized' 5 2).*)


(* basically [fold] from Poly.v*)
Fixpoint FSetFold (f: nat->FSet.t->FSet.t) (l: list nat) (b: FSet.t)
                         : FSet.t :=
  match l with
  | nil => b
  | h :: t => f h (FSetFold f t b)
  end.

(* Compute (show (FSetFold FSet.add [1;2;3] FSet.empty)).*)

(* function converting a list of nats to an FSet *)
Fixpoint listNatToFSet (l : list nat) : FSet.t :=
  FSetFold FSet.add l FSet.empty.

(* generator for FSets, takes *)
Fixpoint genFSet (n : nat) (len : nat) : G FSet.t :=
  (* n: elements can be any nat less than n *)
  (* len: max size of the FSets *)
  liftM listNatToFSet (genListSized len (choose (0,n))).

(*Sample (genFSet 5 2).*)


(****************************************************************)

(* set of sets of nodes, i.e. sets of FSets *)
Module FSys := Make FSet.

Instance showFSys: Show FSys.t :=
  {| show s := show (FSys.elements s)
  |}.

(* some examples *)
Definition test2 := FSys.union (FSys.singleton test) (FSys.empty).

Compute FSys.mem test test2. (* evaluates to `true` *)
Compute FSys.subset FSys.empty test2. (* evaluates to `true` *)

(*now we're ready to make our FSys generator!*)

Fixpoint genFSys (n : nat) (len : nat) (sys_sz : nat) : G FSys.t :=
  (*sys_sz: number of FSets in a generated FSys*)
  match sys_sz with
  | 0 => ret FSys.empty
  | S sys_sz' =>
    liftM2 FSys.add (genFSet n len) (genFSys n len sys_sz')
  end.

(* optionally, slightly more interesting generator *)
Fixpoint genFSys' (n : nat) (len : nat) (sys_sz : nat) : G FSys.t :=
  (*sys_sz: max number of FSets in a generated FSys*)
  match sys_sz with
  | 0 => ret FSys.empty
  | S sys_sz' =>
    freq [ (1, ret FSys.empty) ;
           ((Nat.square sys_sz), liftM2 FSys.add (genFSet n len) (genFSys n len sys_sz'))
               ]
  end.

(* Sample (genFSys 3 3 3).*)
(* Sample (genFSys 5 3 3).*)
(****************************************************************)

(* useful QuickChick types from QC.v, repeated here for convenience:

Inductive Result :=
  | Success : Result
  | Failure : forall {A} `{Show A}, A -> Result.

Arguments Failure {A} {H} _.

Instance showResult : Show Result :=
  {
    show r := match r with
              | Success => "Success"
              | Failure a => "Failure: " ++ show a (* edited from _ _ a*)
              end
  }.

Definition Checker := G Result.

Class Checkable A :=
  {
    checker : A -> Checker
  }.

Instance showUnit : Show unit :=
  {
    show u := "tt"
  }.

(** The failure cases in the [bool] and [Dec] checkers don't need to
    record anything except the [Failure], so we put [tt] (the sole
    value of type [unit]) as the "failure reason." *)

Instance checkableBool : Checkable bool :=
  {
    checker b := if b then ret Success else ret (Failure tt)
  }.

Instance checkableDec `{P : Prop} `{Dec P} : Checkable P :=
  {
    checker p := if P? then ret Success else ret (Failure tt)
  }.

(* Slightly modified to take an additional generator *)
Definition forAll {A B C : Type} `{Show A} `{Checkable C}
                  (ga : G A) (gb : G B) (f : A -> B -> C)
                : Checker :=
  a <- ga ;;
  b <- gb ;;
  r <- checker (f a b) ;;
  match r with
  | Success => ret Success
  | @Failure _ _ b => ret (Failure (a,b))
  end.
 *)

(****************************************************************)
(* properties to test *)
Definition q3 (f1 f2 f3 : FSet.t) (F : FSys.t) (n : nat) : bool :=
  (FSys.mem f1 F) && (FSys.mem f2 F) && (FSys.mem f3 F) &&
  negb  (FSet.subset (all_nodes n) (FSet.union (FSet.union f1 f2) f3)).
(* intuition: q3 is a property necessary for system-wide consistency,
    which says that no 3 fail sets in the system cover all nodes.*)

Definition q3all (F : FSys.t) (n : nat) :=
  forall f1 f2 f3, is_true (q3 f1 f2 f3 F n).

Definition q3all' (f1 f2 f3 : FSet.t) (F : FSys.t) (n : nat) :=
  (q3 f1 f2 f3 F n).


(****************************************************************)

(* chooseFSet: given FSys, this is a generator that chooses
     one FSet in FSys. *)
Check FSys.elements.
Definition chooseFSet (fsys : FSys.t) : G FSet.t :=
  elems_ FSet.empty (FSys.elements fsys).

(* genTriples: given FSys, this is a generator that will
   repeatedly choose 3 FSets in FSys at random,
   and returns a list of k such triples. *)
Fixpoint genTestTriples (k : nat) (fsys : FSys.t)
  : G (list (FSet.t*FSet.t*FSet.t)) :=
  let g3 :=
      f1 <- (chooseFSet fsys) ;;
         f2 <- (chooseFSet fsys) ;;
         f3 <- (chooseFSet fsys) ;;
      ret (f1,f2,f3) in
  vectorOf k g3.

(*********
   usage: replace n, len, sys_sz in the query below with desired parameters
  output: if there are 3 sets f1 f2 f3 in F that cover 0..n,
          print f1 f2 f3

QuickChick
  (forAll (genFSys n len sys_sz) (fun fs =>
      forAll (genTestTriples list_len fs) (fun l =>
           whenFail 
            (String.concat "" (List.map (fun '(f1,f2,f3) =>
                                      if  (negb (q3 f1 f2 f3 fs n))
                                      then (show ("failed FSet:",f1,f2,f3))
                                      else "") l))
            (List.forallb (fun '(f1,f2,f3) =>  ( (q3 f1 f2 f3 fs n))) l)))).
*)

(*the following call to QuickChick will sometimes generate an empty system;
  just try calling it again.*)
QuickChick
  (forAll (genFSys 5 3 3) (fun fs =>
      forAll (genTestTriples 5 fs) (fun l =>
           whenFail 
            (String.concat "" (List.map (fun '(f1,f2,f3) =>
                                      if  (negb (q3 f1 f2 f3 fs 5))
                                      then (show ("failed FSet:",f1,f2,f3))
                                      else "") l))
            (List.forallb (fun '(f1,f2,f3) =>  ( (q3 f1 f2 f3 fs 5))) l)))).
