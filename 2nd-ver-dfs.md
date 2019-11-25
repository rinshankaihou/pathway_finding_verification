# Algorithm (naive_dfs.v)
Usage: set **-impredicative-set** and run to the end. Other files are not important at all.

The examples are based on the configuration of the AA airport. Feel free to add your test cases.

Currently we are only using the definitions in vertices.v in the library.

# Spec
Currently there is no formal spec for the input nor the output. (TODO)

Refer naive_dfs.v for the definitions. The entry point of the algorithm is find_path_wrapper.

# Notes
Check out this library https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/fingraph.v, which has a dfs implemented, but Ke does not understand the code. TODO Consider using this library.

# Using the GraphBasics library
1. The GraphBasics lab is old, we need to use **-impredicative-set** option to launch.
    - in vscoq, you need to add "coqtop.args"
    - in coqide, append **-impredicative-set** in Tools->Coqtop Arguments.
    - It may cause inconsistency?  see "https://github.com/coq/coq/wiki/Impredicative-Set".
2. Use make to build the ".vo" files.
3. You need to use **From GraphBasics Require Export xxx** instead of just require export. 

# Contributions
1. Siyuan completed and modified the algorithms in functions.v as well as in *.py in the folder /code. BTW Ke thinks 'code' is a name that precisely represents the nature of the objects contained in the folder. 
2. Ke modified Siyuan's functions in naive_dfs.v.
