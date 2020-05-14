# Setup

## Environment

| Environment | Recommand | Ours |
| ---- | ---- | ---- |
| System | Linux, Mac OS X or Windows WSL2 | 5.4.31-1-Manjaro |
| Opam | 2.0 or higher | 2.0.4
| Opam switch | 4.08 or higher | 4.08.1 ocaml-base-compiler |
| Coq | 8.10.2 | 8.10.2 |

Though the listed environment is not necessarily required for you to run Coq, we still highly recommend you to follow our setup, or there may exist some potential issues. We don't guarantee our code can support all environments.

## Dependency
[math-comp](https://github.com/math-comp/math-comp) package.

[CoqHammer](https://github.com/lukaszcz/coqhammer) with all four ATPs. 

| name | version |
| ---- | ---- |
| CoqHammer | 1.1.1 for Coq 8.10 |
| Vampire | 4.2.2 |
| E | 2.4 |
| z3_tptp | 4.8.7.0 |
| cvc4 | 1.7 | 

Since the CoqHammer is a machine-learning-based proof automation tool, we recognized that many factors can affect whether the proof or reconstruction is successful. This is the reason why we strongly suggest you to use exactly the same environment setup as ours. 

We also recommend you to prepare a high performance CPU to make the code. Low performance may cause the ```hammer``` tactic takes too long to find a proof, so it may assert an error. Based on our experiment, the code can be successfully compiled on:
   - i7-9750H on Linux for 5 ~10 minutes
   - i9-9880H on Windows WSL2 for around 10 minutes

Otherwise, if you encounter any failure related to ```hammer``` tactic, please refer to the last section.


# Make and Extraction
We have a nice makefile.
   - ```make``` : compile all the codes except for ```Extraction.v```
   - ```make clean``` : remove all temporary files and compiled files

Or you can type ```coqc -Q . Taxiway file.v``` to compile a single file.

If you want to extract the algorithm into OCaml, execute ```Extraction.v``` interactively.


# File Description
1. ```Types.v``` : The type definition include graph encoding and intermediate state.
2. ```To_complete.v``` : The expansion algorithm from undirected (naive) graph to directed expanded (complete) graph.
3. ```Find_path.v``` : The find-path algorithm of finding all possible path(arc) on directed expanded graph.
4. ```To_naive.v``` : The downward map from path(arc) to path(edge).
5. ```Correctness.v``` : The proof for the correctness of find-path algorithm on directed expanded graph.
6. ```Downward.v``` : The proof for the downward preservation of correctness of the downward map.
7. ```Lifting.v``` : The proof for the partial identity of expansion map and downward map.
8. ```Example.v``` : Some examples in Ann Arbor airport. It can give you an intuitive understanding on how our algorithm works.
9. ```Extraction.v``` : Extract the code to OCaml.



# Possible Issues and Solutions
1. ```ATPs fail to find a proof.``` This is probably because the time limit for ATP is too short for your CPU performance to find a proof. Please add ```Set Hammer ATPLimit n.``` (n is the time limit, default is 10, we recommend 20) and ```Hammer_cleanup.``` command anywhere before the failed tactic. 
2. ```Fail to reconstruct the proof.``` This is because the time limit for reconstruction is too short for the reconstruction to finish. Please add ```Set Hammer ReconstrLimit n.``` (n is the time, default is 10, typically 20 is enough) command before the failed tactic. 