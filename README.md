# Theory of Reach

This is the Agda accompaniment for the paper [Towards a Theory of Reach](http://www.cs.nott.ac.uk/~gmh/reach.pdf).

The agda implementation for the minimal language is in the [Basic](https://github.com/JonFowler/theoryofreach/tree/master/Basic) folder with components:
- Subs.agda - definition of substitution
- Exp.agda - definition of minimal language, small step semantics + reachability
- LazyNarrowing.agda - definiton of lazy narrowing reduction + forward reachability 
- Sound.agda - soundness of lazy narrowing
- Complete.agda - completeness of lazy narrowing
- WellFound.agda - well foundness used in completeness, this is currently a well foundness specific to lazy narrowing and not as general as the well foundness stated in paper

The agda implementation for the language extended with application and lambda expressions is in the [Func](https://github.com/JonFowler/theoryofreach/tree/master/Basic) folder. The Exp, LazyNarrowing, Sound and Complete modules are extended.
