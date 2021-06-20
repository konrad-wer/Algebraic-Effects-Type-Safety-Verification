# Algebraic Effects Type-Safety Formal Verification in Coq

Coq formalization of the type safety theorem for the calculus from ["An Introduction to Algebraic Effects and Handlers"](https://www.sciencedirect.com/science/article/pii/S1571066115000705) by Matija Pretnar (theorem 4.2 in the paper).

### Compilation

```bash
coq_makefile -f _CoqProject *.v -o Makefile
make
```

*Maps.v file comes from ["Software Foundations"](https://softwarefoundations.cis.upenn.edu/) book.