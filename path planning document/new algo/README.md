# A new pathway finding algorithm

### Preface
This algorithm's main idea is duality between graphs. Other properties follow immediately. Credit: this idea is due to Zheyu Shen.

### Assumptions

1. Each taxiway has a unique name, and does not intersect itself.
2. For any two different taxiways, they can have at most 1 intersection.
3. In order to transform this graph to a dual, every node of our interest in this graph should be an intersection point. Therefore for those node of degree one(D,E,F) - the input/output nodes for the case of Ann Arbor, a dummy fake taxiway (d, e, f) are added to create intersections, and dummy fake taxiways does not intersect other taxiways.
4. I forgot why I included dummy taxiway g. Maybe it is not important.

### Notation
***Alert***: I feel like the following description of the dual graph is making things even more confusing, also the description of the pseudo code involves a severe amount of abuse of notation. **It might be easier for readers to look at the picture and figure out what is going on.**

Paren indicates the naming in the pseudo code.

*G* (graph 1 in the picture): a **naive graph** such that each node has a unique *node name* (**Node**), but edges may share a same name (**TaxiwayName**).
*D* (graph 2 in the picture): The dual of *G*. 

Informally, a mapping from *G* to *D* does such: each **Node** in *G* corresponds to an edge in *D*, and each edge in *G* corresponds to a **Node** in *D*. Corresponding elements preserve the same name. So now each node in *D*  is a taxiway (**TaxiwayName**) and is unique, whereas each edge in *D*  is a **Node** and can have the same *node name*.

  ![duality]](Algo.jpg)
  
### More Notation
The following algorithm works on *D*, and **Node** refer to the name of an edge in *D* (capital letters in the picture), while **TaxiwayName** is the name of a node in *D*.

Node := [A-F]

N1 := Node

N2 := Node

TaxiwayName := [a-f]

TaxiwayNames := TaxiwayName*

ATC := N1 N2 TaxiwayNames

f := TaxiwayNames.first

l := TaxiwayNames.last

attached(n : Node, e : TaxiwayName) : True iff a node n is attached to an edge called e.

connected(t1 : TaxiwayName, t2 : TaxiwayName ): True iff the nodes t1 and t2 are connected by a single edge

### Pseudocode
This is a rewrite of the pseudocode in the picture above for clarity.
 ```
 SEARCH(ATC):
	if !attached(N1, f) || !attached(N2, l)
		fail
	cur_pos = N1
	NodeList = []
	for index in enumerate(TaxiwayNames):
		if !connected(TaxiwayNames[i], TaxiwayNames[i+1]) # ignore out of bound indexing
			fail
		NodeList.push(get_node(TaxiwayNames[i], TaxiwayNames[i+1]))
	return N1 + NodeList + N2
 ```
 
### Example
	SEARCH(D E cba)= DACE
	SEARCH(D E ca)= DBE

### Remarks
1. The algorithm outputs are all names of Nodes of intersections where the aircraft turns onto a new taxiway, for example 

		SEARCH(D E ca)= DBE
ignores Node *A* and Node *C* in *G* - the other intersections that are crossed along the way, but this missing can be filled easily, since every two consecutive Nodes are on the same *Pathway*.

2. The algorithm seems to output a valid path when there is one, and fail when there is not. The path does not allow U-turn within the same taxiway. **TODO** is it *really* correct?

3. Additionally, if the assumption holds, the dual graph seems to ensure that there is at most one path.

4. Looks like this dual graph works for ATC of the form (N1 N2 TaxiwayNames), where N1 and N2 are any Nodes.
