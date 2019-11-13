find_path(start_node, end_node, taxiway_names):
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

get_intermediate_nodes(node, current_taxiway, next_taxiway):
    for i in enumerate(neighbors(node)): // in the original graph!
        if get_edge_name(node, neighbors(node)[i]) == taxiway:
            current_node = neighbors(node)[i]
            prev_node = node
            node_list = []
            while (true):
               temp = get_neighbor_not_prev(current_node, prev_node, taxiway)
               # should only be 1 of these according to assumptions
               if temp == null:
                   break out of while loop and continue to next for loop iteration
               node_list.append(temp)
               if is_attached(temp, next_taxiway):  ##node is in taxiway
                   return node_list
               prev_node = current_node
               current_node = temp
    return null

##############################################################

get_intermediate_nodes(node1, cur_taxi, next_taxi):
    neighbors = neighbor(node1, cur_taxi) # neighbors will have length <= 2 unless the taxiway is self-intersecting
    node_list = intermediate_nodes(node1, node1, cur_taxi, next_taxi, neighbors[0])
    if node_list is None && len(neighbors) > 1:
        node_list = intermediate_nodes(node1, node1, cur_taxi, next_taxi, neighbors[1])
    return node_list

intermediate_nodes(pre_node, cur_node, cur_taxi, next_taxi, neighbors):
    if neighbors == [] return None
    else if head(heighbors) == pre_node:
        return intermediate_nodes(pre_node,cur_node, cur_taxi, next_taxi, rest(neighbors))
    else:
        if is_on_taxiway(head(neighbors),next_taxi) == true: 
            return head(neighbors)
        else
            return head(neighbors) :: intermediate_nodes(cur_node, head(neighbors), cur_taxi, next_taxi, neighbor(head(neighbors), cur_taxi))


###############################################################

get_last_segment(node1, node2, taxiway):
    for i in enumerate(neighbors(node1)): // in the original graph!
        if get_edge_name(node1, neighbors(node1)[i]) == taxiway:
            current_node = neighbors(node1)[i]
            prev_node = node1
            node_list = []
            while (true):
               temp = get_neighbor_not_prev(current_node, prev_node, taxiway)
               // should only be 1 of these according to assumptions
               if temp == null:
                   break out of while loop and continue to next for loop iteration
               node_list.append(temp)
               if temp == node2:
                   return node_list
               prev_node = current_node
               current_node = temp
    return null

################################################################
get_last_segment(node1, node2, taxiway):
    neighbors = neighbor(node1, taxiway) # neighbors will have length <= 2 unless the taxiway is self-intersecting
    node_list = last_segment(node1, node1, node2, taxiway, neighbors[0])
    if node_list is None && len(neighbors) > 1:
        node_list = last_segment(node1, node1, node2, taxiway, neighbors[1])
    return node_list

# suppose we defined the neighbor() the nodes on a certain taxiway
last_segment(pre_node, cur_node,aim_node, taxiway, neighbors):
    if neighbors == [] return None
    else if head(heighbors) == pre_node:
        return last_segment(pre_node,cur_node, aim_node, taxiway, rest(neighbors)) #for
    else if head(neighbors) == aim_node: #(should be only one(if exists))
        # we're assuming that it exists, or it will be done in ==[]
        # for this case, it's done
        return head(neighbors)
    else: # if head(neighbors) != pre_node or aim_node
        return head(neighbors) :: last_segment(cur_node, head(neighbors), aim_node, taxiway, neighbor(head(neighbors)))

# get_neighbor_not_prev(current_node, prev_node, taxiway)
# - Gets the neighbor of the current node that is not equal to the previous node on taxiway. Returns null if no such node exists

# is_attached(node, taxiway)
# - Returns true if node has an out-edge (directed) or edge (undirected) with label ‘taxiway’; returns false otherwise
