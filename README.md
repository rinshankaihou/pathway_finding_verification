# Using the lab
1. The GraphBasics lab is old, we need to use **-impredicative-set** option to launch.
    - in vscoq, you need to add "coqtop.args"
    - It may cause inconsistency, see "https://github.com/coq/coq/wiki/Impredicative-Set".
2. Using make to build the ".vo" files.
3. You need to use **From GraphBasics Require Export xxx** instead of just require export. 