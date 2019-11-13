# Using the library
1. The GraphBasics lab is old, we need to use **-impredicative-set** option to launch.
    - in vscoq, you need to add "coqtop.args"
    - It may cause inconsistency, see "https://github.com/coq/coq/wiki/Impredicative-Set".
    - I don't know whether it's okey, or need to rewrite it.
2. Using make to build the ".vo" files.
3. You need to use **From GraphBasics Require Export xxx** instead of just require export. 

# The code
1. Siyuan He write the "functions.v", Ke Du did with the definition. "function.v" need to import some definitions, but we're just imaging the definitions.
2. There're still many things need to be changed...
3. We need to work further on the definitions.