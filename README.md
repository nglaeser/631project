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
- [x] `in` function: `in : FSet -> FSys -> bool`
    - This is the `mem` function
- [x] `Show`
- [x] Generator to generate `f1 f2 f3` for the Prop below
- [x] `Checkable` type with `check` constructor to be able to use `QuickChick (forAll (generator def)).`
- [ ] get `QuickChick( ... q3all ).` to work

## Other links

- [Proposal](https://docs.google.com/document/d/1lFPreml7LgslPnTjjdDfHuVF2pesquiQE24GpgWXhmI/edit?usp=sharing)
- [Writeup](https://docs.google.com/document/d/1AtpoAKTTFqaedvNnEK_a1VNv1QCHdklmnarx29TzXEo/edit?usp=sharing)
