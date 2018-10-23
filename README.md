# mentiroso
A theorem prover / type checker based on classical logic

Mentiroso is designed to eventually be an extensible theorem prover. It is loosely inspired by Metamath and Coq.

The fundamental object that Mentiroso is concerned with is the Term.
A Term is essentially just an ADT in the host language, which resembles an AST in some notation.

Terms correspond to values, types, kinds, sorts, and so on up the hierarchy.

The two fundamental things you can do with a Term are get its type (which is also a Term) and perform substitutions.
Mentiroso currently has two notions of a substitutable thing. A Var is an opaque type, similar to the 
`P` in the formula `P \/ ~ P` in classical sentential logic. It has no inherent meaning and substitution is only
legal if the thing replacing `P` is itself a type and not something higher in the hierarchy.

A Metavar can be replaced by anything well-formed, including values. In this setting `4 -> 4` is (vacuously) true because
`4` is not inhabited. This is a little bit different than most settings where it is not possible to ask questions
about the inhabits of values.

Every well-formed Term is a witness of the truth of *something*. For instance, `4` is a proof that `Integer` is true.

The other part to Mentiroso is the test suite.

The core type system is going to be (and is in the process of being) checked with a bunch of quickcheck properties.

A quickcheck property is limited to expressing a first-order formula with only universal quantifiers.

A major goal of this project is to nail down enough of these properties in the test suite so that it's possible to trust Mentiroso's proofs
or proofs written in an extension of the original system.

Another goal of Mentiroso, which I haven't figured out yet, is serializing ground terms (i.e. without metavariables)
into other languages. This way Mentiroso can still be useful despite being an untrusted part of the toolchain.
