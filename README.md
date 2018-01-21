# dancinglinks
## Knuth's Dancing Links algorithm in Java

Implementation of ideas found in Knuth's Fascicle 5C of TAoCP.

The text describes variants of the Dancing Links algorithm, which can be used to solve the
Exact Cover (XC) problem. One has a set of *items*, together with a set of *options* (which are 
each nonempty subsets of the items), and asks whether there is a subset of the options which
will *exactly cover* the items (in the sense that each item occurs exactly once in the 
chosen options).

Knuth proposes a simple text representations for XC problems which this code can read:
The first line lists the items, separated by whitespace; each following line is an option,
consisting of whitespace-separated items.

For example, the problem specification

```
a b c d e f g
c e
a d g
b c f 
a d f
b g 
d e g
```

is solved if we select the first, fourth and fifth options (`c e`, `a d f`, `b g`) and in 
fact this is the only solution.

In code, we can say:

```java
ExactCoverProblem p = ExactCoverProblem.parseFrom("a b c d e f g\nc e\na d g\nb c f\na d f\nb g\nd e g");
```

Then `p.solutions()` is a `Stream<List<Integer>>` which will have one element: the list `[3, 4, 0]`, 
indicating which options (counting from zero) form the solution.

The stream is lazy: calling `solutions()` only pays the cost of setting up the problem tableau. 
Each demand for a new element of the stream will provoke a search for the next distinct solution,
which will stop as soon as one is found. The search for solutions will be exhaustive if you drain
the whole stream.

Adapters are provided for a few applications of XC that Knuth proposes.

### Sudoku

You can supply a Sudoku problem in the form of a string of 81 digits or dots (indicating an empty
cell), and then geneate a stream of solutions:

```java
String ex28c = ".3. .1. ... " +
                "... 4.. 1.." +
                ".5. ... .9." +
                "2.. ... 6.4" +
                "... .35 ..." +
                "1.. ... ..." +
                "4.. 6.. ..." +
                "... ... .5." +
                ".9. ... ...";
Sudoku.fromBoardString(ex28c).solutions().collect(Collectors.toList())                
// ["934 518 267 762 493 185 851 762 493 285 971 634 649 235 718 173 846 529 418 659 372 327 184 956 596 327 841 ",
//  "934 517 268 862 493 175 751 862 493 275 981 634 649 235 817 183 746 529 417 659 382 328 174 956 596 328 741 "]
```

The solver is fast; it can generate an answer without about 15sm.

### Word Find

You can request the generation of word find puzzles. Just supply the grid witdh and height and 
a list of words to fit in the grid. Words can appear in any of the 8 orientations. The wrapper
generates a stream of solutions as strings (using newlines to separate rows of the grid).

```java
new WordFind(8, 8, Arrays.asList("gandalf", 
                                 "frodo", 
                                 "boromir", 
                                 "merry", 
                                 "pippin", 
                                 "aragorn", 
                                 "samwise", 
                                 "legolas", 
                                 "gimli", 
                                 "gollum", 
                                 "ring", 
                                 "sauron")).solutions().limit(1)
```
creates a stream which will produce the solution
```
G A N D A L F B
S N Y R R E M O
A P I F A G U R
M I L R G O L O
W P M O O L L M
I P I D R A O I
S I G O N S G R
E N S A U R O N
```
A dot character is used for cells that are unused after the packing is achieved; thus in this case we
can see that every cell in the grid participates in the puzzle.

