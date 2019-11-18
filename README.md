# CMSC 631 Project

Erica Blum & Noemi Glaeser

#### Sets of nodes:
```
Inductive FSet (* set of nats between 1 and n (representing nodes), no repeats *)
| empty : FSet
| insert : nat -> FSet -> FSet
| union: FSet -> FSet -> FSet
```
Implement this as a [MSetList](https://coq.inria.fr/library/Coq.MSets.MSetList.html#) which requires elements of OrderedType; example [here](https://stackoverflow.com/questions/44793027/example-uses-of-msets-in-coq) and [here?](https://coq.github.io/doc/master/stdlib/Coq.Structures.OrderedTypeEx.html).

#### Sets of sets of nodes:
```
Inductive FSys (* set of FSets *)
| empty : FSys
| insert : FSet -> FSys -> FSys
```
Implement this as a [MSetWeakList](https://coq.inria.fr/library/Coq.MSets.MSetWeakList.html#) which requires elements of DecidableType.

#### Need:
- `in` function: `in : FSet -> FSys -> bool`
- `Show`
- Generator to generate `f1 f2 f3` for the Prop below

```
Prop : forall (f1 f2 f3 : FSet) (F : FSys),
    (f1 in F) -> (f2 in F) -> (f3 in F) ->
    ~([1..n] subset (f1 union f2 union f3)).
```

## Other links

- [Finite Sets library](https://coq.inria.fr/library/Coq.Sets.Finite_sets.html): probably more complicated to use than the libraries linked above
