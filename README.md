# Taxiway Finding Algorithm Verification

A taxiway finding algorithm with correctness proof, implemented in Coq. 

The code is for paper "*Veriﬁcation of an Airport Taxiway Path-Finding Algorithm*", DASC 2020, submitted and waiting for decision now.

## Setup

### Environment

| Environment | Recommended | Ours |
| ---- | ---- | ---- |
| System | Linux, Mac OS X or Windows WSL2 | 5.4.31-1-Manjaro |
| Opam | 2.0 or higher | 2.0.4
| Opam switch | 4.08 or higher | 4.08.1 ocaml-base-compiler |
| Coq | 8.10.2 | 8.10.2 |

**Make sure you have best performance** before ***make***, or proof construction may fail. Refer to following sections for trouble shooting.

Though the listed environment is not necessarily required for you to run Coq, we still highly recommend you to follow our setup, or there may exist some potential issues. We don't guarantee our code can support all environments.

### Coq Dependency

[math-comp](https://github.com/math-comp/math-comp) package.

[Coq.IO](http://coq.io/getting_started.html) (for extraction to Ocaml and IO in Coq. See extraction.v)

[CoqHammer](https://github.com/lukaszcz/coqhammer) with all four ATPs.

| name | version |
| ---- | ---- |
| CoqHammer | 1.1.1 for Coq 8.10 |
| Vampire | 4.2.2 |
| E | 2.4 |
| z3_tptp | 4.8.7.0 |
| cvc4 | 1.7 |

Since the CoqHammer is a machine-learning-based proof automation tool, we recognized that many factors can affect whether the proof or reconstruction is successful. This is the reason why we strongly suggest you to use the exactly the same environment setup as ours.

We also recommend you to use a high performance CPU to make the code. Low performance may limit the performance of the ```hammer``` tactic, which may lead to failure in constructing the proof. Based on our experiment, the code can be successfully compiled on:

- i7-9750H on Manjaro for 5 minutes with full CPU occupied
- i9-9880H on Windows WSL2 for around 10 minutes (performance mode on)

Otherwise, if you encounter any failure related to ```hammer``` tactic, please refer to the last section.

## Make and Extraction

We have a nice makefile.

- ```make``` : compile all the codes and extract. If ```hammer``` fails, try ```make``` again without cleaning the cache for ```hammer```.
- ```make extract```: compile the extracted example. 
- ```make clean``` : remove all temporary files, compiled files and extracted files

Or you can type ```coqc -Q . Taxiway file.v``` to compile a single file.

The makefile automatically create the extracted files for you. You can type the command to print the result of an example after you run ```make extract```.

```
./coq_print.native
```



If you don't want to install the IO library, you can execute the alternative code in ```Extraction.v``` and run ```extracion/print_result.ml``` instead. If you just want the pure algorithm code, we extract and store it in ```extraction/path_finding_algorithm.ml``` for you.

## File Description

The meat is all in ```src/```.

1. ```Types.v``` : The type definition include graph encoding and intermediate state.
2. ```To_complete.v``` : The expansion algorithm from undirected (naive) graph to directed expanded (complete) graph.
3. ```Find_path.v``` : The find-path algorithm that finds all possible path(arc) on the directed expanded graph.
4. ```To_naive.v``` : The downward map from path(arc) to path(edge).
5. ```Correctness.v``` : The proof for the correctness of find-path algorithm on directed expanded graph.
6. ```Downward.v``` : The proof for the downward preservation of correctness of the downward map.
7. ```Lifting.v``` : The proof for the partial identity of expansion map and downward map.
8. ```Example.v``` : Some examples of the algorithm running on the Ann Arbor airport.
9. ```Algorithm.v``` : The top-level algorithm, along with the top level theorem stating the correctness of that algorithm.
10. ```Extraction.v``` : Extracting the code to OCaml.
11. ```Example_Wil.v, Example_Dtw.v```: Two extra examples on Willow Run and DTW airport. We provide two path finding examples for each, and you're free to play by yourself.

The ```Example.v``` is used initially to introduce what we're doing for each step and provide an intuitive understanding of the correctness of our theorems. If you want to play with the path finding algorithm, we provide ```Example_Wil.v``` (a small graph) and ```Example_Dtw.v``` (a large airport) for you. You're free to apply the algorithm to any other airports, but make sure you have made all necessary encoding similar to the three examples.

## Possible Issues and Solutions

0. General quick fix: type make again without cleaning anything. 
    -   No joking, a particular case is line 291 in ```Downward.v```.
    -   Almost all problem is due to the performance, and maybe you should cool down your CPU. The proofs are written in Ann Arbor where heat is not welcomed.
1. ```ATPs fail to find a proof.``` This is probably because the time limit for ATP is too short for your CPU to find a proof. Please add ```Set Hammer ATPLimit n.``` (n is the time limit, default is 10, we recommend 20) and ```Hammer_cleanup.``` command anywhere before the failed tactic.
2. ```Fail to reconstruct the proof.``` This is because the time limit for reconstruction is too short for the reconstruction to finish. Please add ```Set Hammer ReconstrLimit n.``` (n is the time, default is 10, typically 20 is enough) command before the failed tactic.
    - We observe that in ```WSL2``` (with high version of hammer), there're some ```hammer``` will suffer this problem. Even the ATP time is very fast, the reconstruction may always fail (even after 30s). We fix some of the cases, but we don't promise everywhere. 
3. Running out of memory. We recommend you [download more ram](https://downloadmoreram.com/).

## Naming Convention

In the code, we don't use the term *undirected* and *directed expanded* because they look similar and have strange abbreviation. Instead, we use'

- ***n*** or ***naive*** for "undirected"
- ***c*** or ***complete*** for "directed (expanded)"

Hereby, when you see *n* and *c* is the code, it is very likely to the indicate *undirected* and *directed*. For example, ```to_N``` means a map from a directed path to a undirected path.
