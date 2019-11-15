# CMSC 631 Project

Erica Blum & Noemi Glaeser

```
Inductive FSet (* set of nats between 1 and n (representing nodes), no repeats *)
| empty : FSet
| insert : nat -> FSet -> FSet
| union: FSet -> FSet -> FSet

Inductive FSys (* set of FSets *)
| empty : FSys
| insert : FSet -> FSys -> FSys
```

Need:
- `in` function: `in : FSet -> FSys -> bool`
- `Show`

```
Prop : forall (f1 f2 f3 : FSet) (F : FSys),
    (f1 in F) -> (f2 in F) -> (f3 in F) ->
    ~([1..n] subset (f1 union f2 union f3)).
```
