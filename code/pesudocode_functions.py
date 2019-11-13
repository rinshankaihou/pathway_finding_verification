
# suppose we defined the neighbor() the nodes on a certain taxiway
# suppose we have a function last_node(node_list) to return the last element
# suppose we have a function drop_last(node_list) to return the list without last element

def get_last_segment(source_node, aim_node, taxiway):
    neighbors = neighbor(source_node, taxiway) # neighbors will have length <= 2 unless the taxiway is self-intersecting
    node_list = last_segment(source_node, source_node, source_node, aim_node, taxiway, [head(neighbors)]) #run the neighbor[0], imaging it exists
    if last_node(node_list) == source_node:     # it is what we want
        return drop_last(node_list)
    else: # imaging there's still a neighbor 
        return drop_last(last_segment(source_node, source_node, source_node, aim_node, taxiway, [last_node(neighbors)]))
#there is a case that there's only one neighbor but a wrong direction
#I don't know whether I can imagine it doesn't exists...



# this will pick one sided from the original point, so we can't use it for both sides
# it may return empty when S->D directly, but we can't break all recursive
# the idea is to add the source S as check, i.e. nodes_list::S
# the reason to put it at last is because the recursive add nodes from beginning
# the source_node is used to passed as checker S
def last_segment(source_node, pre_node, cur_node, aim_node, taxiway, neighbors):
    if neighbors == []  #so in the latter, the head(neighbors) exists and =the next node
        return []   #since recursively used, we can't use none
    else if head(heighbors) == pre_node:    #prohibits the coming back
        return last_segment(source_node, pre_node,cur_node, aim_node, taxiway, rest(neighbors)) 
    else if head(neighbors) == aim_node: 
        return head(neighbors) :: source_node #last node we want + S (as checker)
    else: #if head(neighbors) != pre_node or aim_node: 
        return head(neighbors) :: last_segment(source_node,cur_node, head(neighbors), aim_node, taxiway, neighbor(head(neighbors)))

#============================================================================
# it's similar to the previous function, only change is judge if ends
def get_intermediate_nodes(source_node, cur_taxi, next_taxi):
    neighbors = neighbor(source_node, cur_taxi) # neighbors will have length <= 2 unless the taxiway is self-intersecting
    node_list = intermediate_nodes(source_node, source_node, source_node, cur_taxi, next_taxi, [head(neighbors)])
    if last_node(node_list) == source_node:    
        return drop_last(node_list)
    else: 
        return drop_last(last_segment(source_node, source_node, source_node, aim_node, taxiway, [last_node(neighbors)]))


def intermediate_nodes(source_node, pre_node, cur_node, cur_taxi, next_taxi, neighbors):
    if neighbors == [] 
        return []
    else if head(heighbors) == pre_node:
        return intermediate_nodes(source_node, pre_node,cur_node, cur_taxi, next_taxi, rest(neighbors))
    else:
        if is_on_taxiway(head(neighbors),next_taxi) == true: 
            return head(neighbors) :: source_node   #??? should the node on the next_taxi be added into the list?
        else
            return head(neighbors) :: intermediate_nodes(source_node, cur_node, head(neighbors), cur_taxi, next_taxi, neighbor(head(neighbors), cur_taxi))

#============================================================================

def find_path(start_node, end_node, taxiway_names):
    path = [start_node]
    current_node = start_node
    for i in enumerate(taxiway_names): # do not allow out of bounds indexing
        path_segment = get_intermediate_nodes(current_node, taxiway_nodes[i], taxiway_nodes[i+1])
        if path_segment == null:
            fail
        path.append(path_segment)
        current_node = path[len(path) - 1]
    path_segment = get_last_segment(current_node, end_node, taxiway)
    if path_segment == null:
        fail
    path.append(path_segment)
    return path 