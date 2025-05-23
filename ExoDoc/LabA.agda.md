```


-- Please do not distribute solutions but let people learn by doing the exercices.
```
# Beyond this course
## Key Points
- more awsomeness
```
{-# OPTIONS --allow-unsolved-metas #-}

module LabA where 
```

# To Be Continued
--MD ## Agda syntax
- I have chosen simple identifiers to smooth the transition from Haskell to Agda
- Agda heavily relies on unicode, in the standard library: 
    - `==` is named `≡`
    - `Nat` is named `ℕ`
    - `<=` is named `≤`
    - `neg` is named `¬`
    - etc.

## Agda offers more concepts
Please have a look at the documentation for 
- records
- meta programming
- codinduction
- cubical 
- ... 

## References 
- here are a few more material about Agda and dependent types

### Agda distribution
- doc, https://agda.readthedocs.io/en/v2.6.3/ 
  the official documentation contains a list of tutorials: https://agda.readthedocs.io/en/v2.6.3/getting-started/tutorial-list.html
- the development version: https://github.com/agda/agda
- the standard library: https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md

### Other Teaching Material
- Philip Wadler et al., https://plfa.github.io
- Samuel Mimram, http://www.lix.polytechnique.fr/Labo/Samuel.Mimram//teaching/INF551/
- Xavier Leroy, https://www.college-de-france.fr/chaire/xavier-leroy-sciences-du-logiciel-chaire-statutaire
  numerous teaching videos **in french** about depedent types, certified compilation and other interesting topics

### Book
- Sandy Maguire, Certainty by Construction, https://leanpub.com/certainty-by-construction
- Aaron Stump, Verified Functional Programming in Agda, https://www.morganclaypoolpublishers.com/catalog_Orig/product_info.php?products_id=908

### Research Articles
- tba

### Blog Posts
- tba 

### Other Proof Assistants 
Here are a few other proof assistants, although I have only had a look at Coq, and the Idris book is yearning at me. 
#### Coq 
- Coq, https://coq.inria.fr
- an industrial strength application of Coq: Compcert a C certified compiler, https://compcert.org
#### Idris
- https://www.idris-lang.org
#### Lean
- https://leanprover.github.io
```
--MD
```
### Formal Methods in Industry
- [IOHK](https://iohk.io/en/), a blockchain company working on Cardano, uses Agda to formalize and verify their [transaction models](https://github.com/IntersectMBO/formal-ledger-specifications) or to verify [smart contract languages](https://github.com/omelkonian/formal-bitml)
- [Serokell](https://serokell.io) apparently uses Agda
- Amazon Web Services uses Lean 4 to formalize their [authorization policy language](https://www.amazon.science/publications/cedar-a-new-language-for-expressive-fast-safe-and-analyzable-authorization)
- [Nomadic Labs](https://www.nomadic-labs.com) formalizes the Tezos block chain in Coq, and also [Formal Land](https://formal.land), who made the [coq-of-rust](https://github.com/formal-land/coq-of-rust) tool to be able to check Rust with Coq
- in aerospace, there are a lot of companies using formal methods, such as Airbus, NASA and others
- more generally, there's a [list](https://github.com/ligurio/practical-fm) of companies that use formal methods
```

```
# Last but not least
- I would like to thank:
- Simon Boulier, Ronan-Alexandre Cherrueau, Julien Cohen, Herve Grall, Guillaume Munch-Maccagnoni, Pierre-Marie Pedrot, Josselin Poiret, Nicolas Tabareau, and members of the Gallinette team for their help with Coq and dependent types
    - the FIL A2 2021-24 students who have tested this material
    - Ulf Norell, Catarina Coquand and anybody involved in Agda development (your language rocks)

