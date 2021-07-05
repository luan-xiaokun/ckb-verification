# CKB Verification
 A formal model of [CKB consensus protocol](https://github.com/nervosnetwork/rfcs/blob/master/rfcs/0020-ckb-consensus-protocol/0020-ckb-consensus-protocol.md) in Coq and proof of quiescent consistency property.

 ## Requirements
 * [Coq 8.12 or later](https://coq.inria.fr)
 * [Mathematical Components ssreflect 1.11.0](https://math-comp.github.io)
 * [Mathematical Components finmap 1.5.0](https://github.com/math-comp/finmap)

## Building
We recommend installing the Coq requirements via [OPAM](https://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.12.0 coq-mathcomp-ssreflect.1.11.0 coq-mathcomp-finmap.1.5.0
```

Then run `make` in the project root directory, this will check all the definitions and proofs.
