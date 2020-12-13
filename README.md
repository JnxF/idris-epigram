# Idris EPIGRAM
![Idris workflow](https://github.com/jnxf/safe-epigram/workflows/Idris%20workflow/badge.svg)
![Hits](https://visitor-badge.glitch.me/badge?page_id=jnxf.safe-idris)
[![GitHub stars](https://img.shields.io/github/stars/JnxF/safe-epigram.svg)](https://GitHub.com/JnxF/safe-epigram/stargazers/)
[![GitHub forks](https://img.shields.io/github/forks/JnxF/safe-epigram.svg)](https://GitHub.com/JnxF/safe-epigram/network/)
[![GitHub repo size in bytes](https://img.shields.io/github/repo-size/JnxF/safe-epigram.svg)](https://github.com/JnxF/safe-epigram)
[![GitHub contributors](https://img.shields.io/github/contributors/JnxF/safe-epigram.svg)](https://GitHub.com/JnxF/safe-epigram/graphs/contributors/)
[![GitHub license](http://img.shields.io/github/license/JnxF/safe-epigram.svg)](https://github.com/JnxF/safe-epigram/blob/master/LICENSE)

Idris implementation of a type-correct, stack-safe compiler including exception handling.

Based on the following papers:

* [_A type-correct, stack-safe, provably correct, expression compiler in Epigram_](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.94.62&rep=rep1&type=pdf)
* [_Dependently-Typed Compilers Don't Go Wrong_](http://www.cs.nott.ac.uk/~pszgmh/well-typed.pdf)

## Report PDF

TBD

## Installation
Install [Idris 1](https://www.idris-lang.org/pages/download.html).

## Usage
```bash
$ idris throw.idr
     ____    __     _
    /  _/___/ /____(_)____
    / // __  / ___/ / ___/     Version 1.3.3
  _/ // /_/ / /  / (__  )      https://www.idris-lang.org/
 /___/\__,_/_/  /_/____/       Type :? for help

Idris is free software with ABSOLUTELY NO WARRANTY.
For details type :warranty.

*throw> compiledProgram
PUSH (VNat 3)
     (STORE "x"
            (LOAD "x"
                  (PUSH (VNat 1)
                        (ADD (STORE "x"
                                    (LOAD "x"
                                          (PUSH (VNat 2)
                                                (ADD (STORE "y"
                                                            HALT))))))))) : Code []
                                                                                 []
                                                                                 []
                                                                                 [("y",
                                                                                   NatTy),
                                                                                  ("x",
                                                                                   NatTy),
                                                                                  ("x",
                                                                                   NatTy)]
```

## Authors

* Francisco Martínez Lasaca
* Morten Skøtt Knudsen
* Jeppe Vinberg

## License
[MIT](https://choosealicense.com/licenses/mit/)